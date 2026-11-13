import unittest
from spop.shell import *


def probes(m):
    return [(m.w.spheres[i].payload, m.w.status[i], m.w.reasons.get(i)) for i in range(len(m.w.spheres))
            if m.w.spheres[i].tag == "probe"]


class ShellTests(unittest.TestCase):
    def test_bash_path_order_and_hash(self):
        m = ubuntu_machine(); sh = Shell(m, "bash")
        sh.run("ls")
        p = probes(m)
        self.assertEqual([x[0][0] for x in p], ["/usr/local/sbin", "/usr/local/bin", "/usr/sbin", "/usr/bin", "/sbin", "/bin"])
        self.assertEqual([x[1] for x in p], ["refused"] * 5 + ["popped"])
        self.assertTrue(all(x[2] == "missing" for x in p[:5]))
        sh.run("ls")
        self.assertEqual(len(probes(m)), 6)                 # hashed: no new probes
        sh.run("export PATH=/bin")
        self.assertIn("path-changed", m.w.reasons.values())
        sh.run("ls")
        self.assertEqual(len(probes(m)), 7)

    def test_path_order_shadows(self):
        m = ubuntu_machine()
        m.mk("linux", "/usr/local/bin/hello", ("exe", "hello", True))
        m.mk("linux", "/usr/bin/hello", ("exe", "hello", True))
        sh = Shell(m, "bash"); sh.run("type hello")
        self.assertIn("/usr/local/bin/hello", sh.output())
        sh.run("export PATH=/usr/bin:/usr/local/bin"); sh.run("type hello")
        self.assertIn("hello is /usr/bin/hello", sh.output())

    def test_type_vs_which(self):
        m = ubuntu_machine(); sh = Shell(m, "bash")
        sh.run("alias ll='ls'"); sh.run("type cd"); sh.run("type ll"); sh.run("which cd")
        out = sh.output()
        self.assertIn("cd is a shell builtin", out)
        self.assertIn("ll is aliased to `ls'", out)
        self.assertEqual(sh.status(), 1)                     # which knows nothing of builtins

    def test_not_found_noexec_and_hook(self):
        m = ubuntu_machine(); m.mk("linux", "/home/me/data", ("data", "x"))
        m.mk("linux", "/home/me/script", ("exe", "hello", False))
        sh = Shell(m, "bash", hook=lambda n: "Command '%s' not found, but can be installed with:\nsudo apt install %s-pkg\n" % (n, n) if n == "htop" else None)
        self.assertEqual(sh.run("nope"), 127); self.assertIn("command not found", sh.output())
        self.assertEqual(sh.run("htop"), 127); self.assertIn("apt install htop-pkg", sh.output())
        self.assertEqual(sh.run("./script"), 126)
        self.assertEqual(sh.run("echo $?"), 0); self.assertTrue(sh.output().endswith("126\n"))
        self.assertEqual(sh.run("false || echo ok && echo more"), 0)
        self.assertTrue(sh.output().endswith("ok\nmore\n"))

    def test_bash_does_not_search_cwd_but_cmd_does(self):
        m = windows_machine(); ubuntu_machine(m)
        m.mk("win", "C:\\Users\\me\\hello.bat", ("exe", "hello", True))
        m.mk("win", "C:\\Windows\\System32\\hello.exe", ("exe", "hello", True))
        cmd = Shell(m, "cmd")
        cmd.run("hello")
        hit = [p for p in probes(m) if p[1] == "popped"][-1]
        self.assertEqual(hit[0][0][0], "C:\\Users\\me"); self.assertEqual(hit[0][0][1], ".BAT")
        m.mk("linux", "/home/me/hello", ("exe", "hello", True))
        bash = Shell(m, "bash")
        self.assertEqual(bash.run("hello"), 127)
        self.assertEqual(bash.run("./hello"), 0)

    def test_cmd_pathext_order_and_case(self):
        m = windows_machine(); cmd = Shell(m, "cmd")
        self.assertEqual(cmd.run("NOTEPAD a.txt"), 0)
        self.assertIn("[notepad a.txt]", cmd.output())
        exts = [p[0][0][1] for p in probes(m)]
        self.assertEqual(exts[:4], [".COM", ".EXE", ".BAT", ".CMD"])
        self.assertEqual(cmd.run("nothing"), 9009)
        self.assertIn("not recognized", cmd.output())
        cmd.run("nothing"); cmd.run("echo %ERRORLEVEL%")
        self.assertTrue(cmd.output().endswith("9009\n"))
        cmd.run("set GREETING=hi"); cmd.run("echo %greeting%")
        self.assertTrue(cmd.output().endswith("hi\n"))
        cmd.run("where notepad")
        self.assertIn("C:\\Windows\\System32\\notepad.exe", cmd.output())

    def test_wsl_interop_and_translation(self):
        m = windows_machine(); ubuntu_machine(m)
        wsl = Shell(m, "bash", env={"PATH": LINUX_PATH + ":/mnt/c/Windows/System32"})
        self.assertEqual(wsl.run("notepad.exe x"), 0)
        self.assertIn("[notepad x]", wsl.output())
        self.assertEqual(wsl.run("notepad"), 127)            # exact filename in this model
        plain = Shell(m, "bash")
        self.assertEqual(plain.run("notepad.exe"), 127)      # appendWindowsPath off
        wsl.run("cd /mnt/c/Users/me"); wsl.run("pwd")
        self.assertTrue(wsl.output().endswith("/mnt/c/Users/me\n"))

    def test_busybox_multicall(self):
        m = busybox_machine(); sh = Shell(m, "bash", env={"PATH": "/bin"})
        sh.run("echo hello > /home/me/f"); sh.run("cat /home/me/f")
        self.assertEqual(sh.run("ls"), 0)
        self.assertIn("f\n", sh.output())
        self.assertEqual(sh.run("busybox --list"), 0)
        self.assertIn("uname", sh.output())
        self.assertEqual(sh.run("busybox uname"), 0)
        self.assertEqual(sh.run("uname"), 0); self.assertTrue(sh.output().endswith("Linux\n"))
        path, pl = m.resolve_link("linux", "/bin/ls")
        self.assertEqual(path, "/bin/busybox")
        # one image, many names: all applet links resolve to the same executable payload
        self.assertEqual(len({m.resolve_link("linux", "/bin/" + n)[1] for n in APPLETS}), 1)

    def test_replay(self):
        m = windows_machine(); ubuntu_machine(m); sh = Shell(m, "bash"); sh.run("ls; type cd; nope")
        self.assertTrue(m.w.verify())

if __name__ == "__main__":
    unittest.main()
