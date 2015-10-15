# Copyright 2011 OpenStack Foundation
# All Rights Reserved.
#
#    Licensed under the Apache License, Version 2.0 (the "License"); you may
#    not use this file except in compliance with the License. You may obtain
#    a copy of the License at
#
#         http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
#    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#    License for the specific language governing permissions and limitations
#    under the License.
"""
Base test class for running non-stubbed tests (functional tests)

The FunctionalTest class contains helper methods for starting the API
and Conductor server, grabbing the logs of each, cleaning up pidfiles,
and spinning down the servers.
"""

import atexit
import errno
import logging
import os
import shlex
import signal
import socket
import sys
import tempfile
import testtools
import textwrap
import time

from six.moves.urllib import parse as urlparse

from ironic.common import utils
from ironic.tests import base

IRONIC_TEST_SOCKET_FD_STR = 'IRONIC_TEST_SOCKET_FD'


class Server(object):
    """Class to start and stop a server during functional testing

    Class used to easily manage starting and stopping a server during
    functional test runs.
    """

    def __init__(self, test_dir, bind_port, sock_obj=None):
        """Creates a new Server object.

        :param test_dir: The directory where all test stuff is kept. This is
                         passed from the FunctionalTestCase.
        :param bind_port: The port to start a server up on.
        :param sock_obj: Socket to use. If None then create socket.
        """

        self.test_dir = test_dir
        self.bind_port = bind_port
        self.sock_obj = sock_obj

        self.verbose = True
        self.debug = True
        self.no_venv = False
        self.conf_file_name = None
        self.conf_base = None
        self.paste_conf_base = None
        self.exec_env = None
        self.needs_database = False
        self.log_file = None
        self.fork_socket = True
        self.process_pid = None
        self.server_module = None
        self.stop_kill = False

    def start(self, expect_exit=True, expected_exitcode=0, logfile=os.devnull,
              **kwargs):
        """Starts the server.

        Any kwargs passed to this method will override the configuration
        value in the conf file used in starting the servers.

        :param expect_exit: The process should exit after being started
        :param expected_exitcode: When the process exits, the exit code it
                                  should return
        :param logile: A path to a file which will hold the stdout/err of the
                       child process.
        """

        # Ensure the configuration file is written
        self.write_conf(**kwargs)

        self.create_database()

        cmd = ("%(server_module)s --config-file %(conf_file_name)s" % {
            "server_module": self.server_module,
            "conf_file_name": self.conf_file_name
        })
        cmd = "%s -m %s" % (sys.executable, cmd)
        # close the socket and release the unused port closer to start time
        if self.exec_env:
            exec_env = self.exec_env.copy()
        else:
            exec_env = {}
        pass_fds = set()
        if self.sock_obj:
            if not self.fork_socket:
                self.sock_obj.close()
                self.sock_obj = None
            else:
                fd = os.dup(self.sock_obj.fileno())
                # FIXME(jlvillal) Do we want this?
                exec_env[IRONIC_TEST_SOCKET_FD_STR] = str(fd)
                pass_fds.add(fd)
                self.sock_obj.close()

        if not os.path.exists(logfile):
            open(logfile, 'w').close()
        self.process_pid = fork_exec(
            cmd,
            logfile=logfile,
            exec_env=exec_env,
            pass_fds=pass_fds)

        self.stop_kill = not expect_exit
        if self.pid_file:
            pf = open(self.pid_file, 'w')
            pf.write('%d\n' % self.process_pid)
            pf.close()
        if not expect_exit:
            rc = 0
            try:
                # Sending zero (0) does nothing if the process is running,
                # otherwise it raises OSError
                os.kill(self.process_pid, 0)
            except OSError:
                raise RuntimeError("The process did not start")
        else:
            rc = wait_for_fork(self.process_pid,
                               expected_exitcode=expected_exitcode)
        # avoid an FD leak
        if self.sock_obj:
            os.close(fd)
            self.sock_obj = None
        return (rc, '', '')

    def write_conf(self, **kwargs):
        """Write the configuration file.

        Writes the configuration file for the server to its intended
        destination.  Returns the name of the configuration file and
        the over-ridden config content (may be useful for populating
        error messages).
        """
        if not self.conf_base:
            raise RuntimeError("Subclass did not populate config_base!")

        conf_override = self.__dict__.copy()
        if kwargs:
            conf_override.update(**kwargs)

        # A config file and paste.ini to use just for this test...we don't want
        # to trample on currently-running Ironic servers, now do we?

        conf_dir = os.path.join(self.test_dir, 'etc')
        conf_filepath = os.path.join(conf_dir, "%s.conf" % self.server_name)
        if os.path.exists(conf_filepath):
            os.unlink(conf_filepath)
        paste_conf_filepath = conf_filepath.replace(".conf", "-paste.ini")
        if os.path.exists(paste_conf_filepath):
            os.unlink(paste_conf_filepath)
        safe_mkdirs(conf_dir)

        with open(os.path.join(conf_dir, 'policy.json'), 'w') as out_file:
            out_file.write(textwrap.dedent("""
                {
                    "admin_api": "role:admin or role:administrator",
                    "show_password": "!",
                    "default": "rule:admin_api"
                }
                """))

        def override_conf(filepath, overridden):
            with open(filepath, 'w') as conf_file:
                conf_file.write(overridden)
                conf_file.flush()
                return conf_file.name

        overridden_core = self.conf_base % conf_override
        self.conf_file_name = override_conf(conf_filepath, overridden_core)

        overridden_paste = ''
        if self.paste_conf_base:
            overridden_paste = self.paste_conf_base % conf_override
            override_conf(paste_conf_filepath, overridden_paste)

        overridden = ('==Core config==\n%s\n==Paste config==\n%s' %
                      (overridden_core, overridden_paste))

        return self.conf_file_name, overridden

    def reload(self, expect_exit=True, expected_exitcode=0, **kwargs):
        """Start and stop the service to reload

        Any kwargs passed to this method will override the configuration
        value in the conf file used in starting the servers.
        """
        self.stop()
        return self.start(expect_exit=expect_exit,
                          expected_exitcode=expected_exitcode, **kwargs)

    def create_database(self):
        """Create database if required for this server."""
        # FIXME(jlvillal) to work with Ironic
        raise Exception("Does not work")

        if self.needs_database:
            conf_dir = os.path.join(self.test_dir, 'etc')
            safe_mkdirs(conf_dir)
            conf_filepath = os.path.join(conf_dir, 'ironic-manage.conf')

            with open(conf_filepath, 'w') as conf_file:
                conf_file.write('[DEFAULT]\n')
                conf_file.write('sql_connection = %s' % self.sql_connection)
                conf_file.flush()

            ironic_db_env = 'IRONIC_DB_TEST_SQLITE_FILE'
            if ironic_db_env in os.environ:
                # use the empty db created and cached as a tempfile
                # instead of spending the time creating a new one
                db_location = os.environ[ironic_db_env]
                os.system('cp %s %s/tests.sqlite' %
                          (db_location, self.test_dir))
            else:
                # FIXME(jlvillal) what is the correct command????
                cmd = ('%s -m ironic.cmd.manage --config-file %s db sync' %
                       (sys.executable, conf_filepath))
                utils.execute(cmd)

                # copy the clean db to a temp location so that it
                # can be reused for future tests
                (osf, db_location) = tempfile.mkstemp()
                os.close(osf)
                os.system('cp %s/tests.sqlite %s' %
                          (self.test_dir, db_location))
                os.environ[ironic_db_env] = db_location

                # cleanup the temp file when the test suite is
                # complete
                def _delete_cached_db():
                    try:
                        os.remove(os.environ[ironic_db_env])
                    except Exception:
                        # FIXME(jlvillal) We should log this
                        raise NotImplementedError
                        # logger.exception(
                        #    "Error cleaning up the file %s" %
                        #    os.environ[ironic_db_env])

                atexit.register(_delete_cached_db)

    def stop(self):
        """Spin down the server."""
        if not self.process_pid:
            raise Exception('why is this being called? %s' % self.server_name)

        if self.stop_kill:
            os.kill(self.process_pid, signal.SIGTERM)
        rc = wait_for_fork(self.process_pid, raise_error=False)
        return (rc, '', '')

    def dump_log(self, name):
        log = logging.getLogger(name)
        if not self.log_file or not os.path.exists(self.log_file):
            return
        fptr = open(self.log_file, 'r')
        for line in fptr:
            log.info(line.strip())


class ApiServer(Server):
    """Server object that starts/stops/manages the API server"""

    def __init__(self, test_dir, port, pid_file=None, sock_obj=None, **kwargs):
        super(ApiServer, self).__init__(test_dir, port, sock_obj=sock_obj)
        self.server_name = 'api'
        self.server_module = 'ironic.cmd.%s' % self.server_name
        self.pid_file = pid_file or os.path.join(self.test_dir, "api.pid")
        self.log_file = os.path.join(self.test_dir, "api.log")

        # self.needs_database = True
        default_sql_connection = 'sqlite:////%s/tests.sqlite' % self.test_dir
        self.sql_connection = os.environ.get('IRONIC_TEST_SQL_CONNECTION',
                                             default_sql_connection)
        self.data_api = kwargs.get("data_api", "ironic.db.sqlalchemy.api")

        self.conf_base = textwrap.dedent("""
        [DEFAULT]
        log_file=logfile.txt
        auth_strategy=noauth
        enabled_drivers=pxe_amt
        host=test-host
        [api]
        host_ip=127.0.0.1
        port=%(bind_port)s
        [conductor]
        api_url=http://192.168.1.10:6385/
        sync_power_state_interval=-1
        [dhcp]
        dhcp_provider=none
        [pxe]
        pxe_append_params=nofb nomodeset vga=normal
        tftp_root=/var/lib/tftpboot
        tftp_master_path=/var/lib/tftpboot/master_images
        """)


class ConductorServer(Server):
    pass


class FunctionalTestCase(base.TestCase):
    """Test case base class for all functional testing

    Base test class for any test that wants to test the actual servers and
    clients and not just the stubbed out interfaces
    """

    inited = False
    disabled = False
    launched_servers = []

    def setUp(self):
        super(FunctionalTestCase, self).setUp()
        self.test_dir = tempfile.tempdir

        self.api_protocol = 'http'
        self.api_port, api_sock = get_unused_port_and_socket()
        self.conductor_port, reg_sock = get_unused_port_and_socket()

        conf_dir = os.path.join(self.test_dir, 'etc')
        utils.safe_mkdirs(conf_dir)

        self.api_server = ApiServer(self.test_dir,
                                    self.api_port,
                                    self.policy_file,
                                    sock=api_sock)

        self.conductor_server = ConductorServer(self.test_dir,
                                                self.conductor_port,
                                                self.policy_file,
                                                sock=reg_sock)

        self.pid_files = [
            self.api_server.pid_file,
            self.conductor_server.pid_file,
        ]
        self.files_to_destroy = []
        self.launched_servers = []

    def tearDown(self):
        if not self.disabled:
            self.cleanup()
            # We destroy the test data store between each test case,
            # and recreate it, which ensures that we have no side-effects
            # from the tests
            self._reset_database(self.conductor_server.sql_connection)
            self._reset_database(self.api_server.sql_connection)
        super(FunctionalTestCase, self).tearDown()

        self.api_server.dump_log('api_server')
        self.conductor_server.dump_log('conductor_server')

    def _reset_database(self, conn_string):
        conn_pieces = urlparse.urlparse(conn_string)
        if conn_string.startswith('sqlite'):
            # We leave behind the sqlite DB for failing tests to aid
            # in diagnosis, as the file size is relatively small and
            # won't interfere with subsequent tests as it's in a per-
            # test directory (which is blown-away if the test is green)
            pass
        elif conn_string.startswith('mysql'):
            # We can execute the MySQL client to destroy and re-create
            # the MYSQL database, which is easier and less error-prone
            # than using SQLAlchemy to do this via MetaData...trust me.
            database = conn_pieces.path.strip('/')
            loc_pieces = conn_pieces.netloc.split('@')
            host = loc_pieces[1]
            auth_pieces = loc_pieces[0].split(':')
            user = auth_pieces[0]
            password = ""
            if len(auth_pieces) > 1:
                if auth_pieces[1].strip():
                    password = "-p%s" % auth_pieces[1]
            sql = ("drop database if exists %(database)s; "
                   "create database %(database)s;") % {'database': database}
            cmd = (
                "mysql -u%(user)s %(password)s -h%(host)s "
                "-e\"%(sql)s\""
            ) % {'user': user,
                 'password': password,
                 'host': host,
                 'sql': sql}
            exitcode, out, err = utils.execute(cmd)
            self.assertEqual(0, exitcode)

    def cleanup(self):
        """Cleanup what we have done.

        Makes sure anything we created or started up in the tests are destroyed
        or spun down
        """

        # NOTE(jbresnah) call stop on each of the servers instead of
        # checking the pid file.  stop() will wait until the child
        # server is dead.  This eliminates the possibility of a race
        # between a child process listening on a port actually dying
        # and a new process being started
        servers = [self.api_server, self.conductor_server, ]
        for s in servers:
            try:
                s.stop()
            except Exception:
                pass

        for f in self.files_to_destroy:
            if os.path.exists(f):
                os.unlink(f)

    def start_server(self,
                     server,
                     expect_launch,
                     expect_exit=True,
                     expected_exitcode=0,
                     **kwargs):
        """Starts a server on an unused port.

        Any kwargs passed to this method will override the configuration value
        in the conf file used in starting the server.

        :param server: the server to launch
        :param expect_launch: true iff the server is expected to
                              successfully start
        :param expect_exit: true iff the launched process is expected
                            to exit in a timely fashion
        :param expected_exitcode: expected exitcode from the launcher
        """
        self.cleanup()

        # Start up the requested server
        exitcode, out, err = server.start(expect_exit=expect_exit,
                                          expected_exitcode=expected_exitcode,
                                          **kwargs)
        if expect_exit:
            self.assertEqual(expected_exitcode, exitcode,
                             "Failed to spin up the requested server. "
                             "Got: %s" % err)

        self.launched_servers.append(server)

        launch_msg = self.wait_for_servers([server], expect_launch)
        self.assertTrue(launch_msg is None, launch_msg)

    def start_with_retry(self, server, port_name, max_retries,
                         expect_launch=True,
                         **kwargs):
        """Starts a server, with retries

        Starts a server, with retries if the server launches but fails to start
        listening on the expected port.

        :param server: the server to launch
        :param port_name: the name of the port attribute
        :param max_retries: the maximum number of attempts
        :param expect_launch: true iff the server is expected to
                              successfully start
        :param expect_exit: true iff the launched process is expected
                            to exit in a timely fashion
        """
        launch_msg = None
        for i in range(max_retries):
            exitcode, out, err = server.start(expect_exit=not expect_launch,
                                              **kwargs)
            name = server.server_name
            self.assertEqual(0, exitcode, "Failed to spin up the %s server. "
                             "Got: %s" % (name, err))
            launch_msg = self.wait_for_servers([server], expect_launch)
            if launch_msg:
                server.stop()
                server.bind_port = get_unused_port()
                setattr(self, port_name, server.bind_port)
            else:
                self.launched_servers.append(server)
                break
        self.assertTrue(launch_msg is None, launch_msg)

    def start_servers(self, **kwargs):
        """Starts the API and Conductor servers on unused ports.

        Any kwargs passed to this method will override the configuration value
        in the conf file used in starting the servers.
        """
        self.cleanup()

        # Start up the API and default conductor server

        # We start the conductor server first, as the API server config
        # depends on the conductor port - this ordering allows for
        # retrying the launch on a port clash
        self.start_with_retry(self.conductor_server, 'conductor_port', 3,
                              **kwargs)
        kwargs['conductor_port'] = self.conductor_server.bind_port

        self.start_with_retry(self.api_server, 'api_port', 3, **kwargs)

    def ping_server(self, port):
        """Simple ping on the port.

        Simple ping on the port. If responsive, return True, else return False.

        :note We use raw sockets, not ping here, since ping uses ICMP and
        has no concept of ports...
        """
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            s.connect(("127.0.0.1", port))
            s.close()
            return True
        except socket.error:
            return False

    def wait_for_servers(self, servers, expect_launch=True, timeout=30):
        """Wait for server to be available.

        Tight loop, waiting for the given server port(s) to be available.
        Returns when all servers are pingable. There is a timeout on waiting
        for the servers to come up.

        :param servers: Server ports to ping
        :param expect_launch: Optional, true iff the server(s) are
                              expected to successfully start
        :param timeout: Optional, defaults to 30 seconds
        :return: None if launch expectation is met, otherwise an
                 assertion message
        """
        now = time.time()
        timeout_time = now + timeout
        replied = []
        while (timeout_time > now):
            pinged = 0
            for server in servers:
                if self.ping_server(server.bind_port):
                    pinged += 1
                    if server not in replied:
                        replied.append(server)
            if pinged == len(servers):
                msg = 'Unexpected server launch status'
                return None if expect_launch else msg
            now = time.time()
            time.sleep(0.05)

        failed = list(set(servers) - set(replied))
        msg = 'Unexpected server launch status for: '
        for f in failed:
            msg += ('%s, ' % f.server_name)
            if os.path.exists(f.pid_file):
                pid = f.process_pid
                trace = f.pid_file.replace('.pid', '.trace')
                if self.tracecmd:
                    cmd = '%s -p %d -o %s' % (self.tracecmd, pid, trace)
                    utils.execute(cmd, raise_error=False, expect_exit=False)
                    time.sleep(0.5)
                    if os.path.exists(trace):
                        msg += ('\n%s:\n%s\n' % (self.tracecmd,
                                                 open(trace).read()))

        self.add_log_details(failed)

        return msg if expect_launch else None

    def stop_server(self, server, name):
        """Stop a server.

        Called to stop a single server in a normal fashion using the stop
        method to gracefully shut the server down.

        :param server: the server to stop
        """
        # Spin down the requested server
        server.stop()

    def stop_servers(self):
        """Stop all the servers.

        Called to stop the started servers in a normal fashion. Note that
        cleanup() will stop the servers using a fairly draconian method of
        sending a SIGTERM signal to the servers. Here, we use the
        ironic-control stop method to gracefully shut the server down.  This
        method also asserts that the shutdown was clean, and so it is meant to
        be called during a normal test case sequence.
        """

        # Spin down the API and default conductor server
        self.stop_server(self.api_server, 'API server')
        self.stop_server(self.conductor_server, 'Conductor server')

        self._reset_database(self.conductor_server.sql_connection)

    def add_log_details(self, servers=None):
        logs = [s.log_file for s in (servers or self.launched_servers)]
        for log in logs:
            if os.path.exists(log):
                testtools.content.attach_file(self, log)


def fork_exec(cmd, exec_env=None, logfile=None, pass_fds=None):
    """Execute a command using fork/exec.

    This is needed for programs system executions that need path searching but
    cannot have a shell as their parent process, for example: ironic-api.  When
    ironic-api starts it sets itself as the parent process for its own process
    group.  Thus the pid that a Popen process would have is not the right pid
    to use for killing the process group.  This patch gives the test env direct
    access to the actual pid.

    :param cmd: Command to execute as an array of arguments.
    :param exec_env: A dictionary representing the environment with
                     which to run the command.
    :param logile: A path to a file which will hold the stdout/err of
                   the child process. This path must already exist.
    :param pass_fds: Sequence of file descriptors passed to the child.
    """
    env = os.environ.copy()
    if exec_env is not None:
        for env_name, env_val in exec_env.items():
            if callable(env_val):
                env[env_name] = env_val(env.get(env_name))
            else:
                env[env_name] = env_val

    pid = os.fork()
    if pid == 0:
        if logfile:
            fds = [1, 2]
            with open(logfile, 'r+b') as fptr:
                for desc in fds:  # close fds
                    try:
                        os.dup2(fptr.fileno(), desc)
                    except OSError:
                        pass
        if pass_fds and hasattr(os, 'set_inheritable'):
            # os.set_inheritable() is only available and needed
            # since Python 3.4. On Python 3.3 and older, file descriptors are
            # inheritable by default.
            for fd in pass_fds:
                os.set_inheritable(fd, True)

        args = shlex.split(cmd)
        os.execvpe(args[0], args, env)
    else:
        return pid


def wait_for_fork(pid, raise_error=True, expected_exitcode=0):
    """Wait for a process to complete

    This function will wait for the given pid to complete.  If the
    exit code does not match that of the expected_exitcode an error
    is raised.
    """

    rc = 0
    try:
        (pid, rc) = os.waitpid(pid, 0)
        rc = os.WEXITSTATUS(rc)
        if rc != expected_exitcode:
            raise RuntimeError('The exit code %d is not %d' %
                               (rc, expected_exitcode))
    except Exception:
        if raise_error:
            raise

    return rc


def safe_mkdirs(path):
    try:
        os.makedirs(path)
    except OSError as e:
        if e.errno != errno.EEXIST:
            raise


def get_unused_port():
    """Returns an unused port on localhost."""
    port, s = get_unused_port_and_socket()
    s.close()
    return port


def get_unused_port_and_socket():
    """Return an unused port and socket on localhost.

    Returns an unused port on localhost and the open socket from which it was
    created.
    """
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.bind(('localhost', 0))
    addr, port = s.getsockname()
    return (port, s)
