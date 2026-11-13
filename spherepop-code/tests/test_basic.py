import unittest
from spop.basic import *


def prog(*lines, **kw):
    b = Basic(**kw)
    for l in lines: b.enter(l)
    return b


class BasicTests(unittest.TestCase):
    def test_print_and_number_format(self):
        b = Basic(); b.enter("PRINT 2+3"); b.enter('PRINT "A";5;"B"'); b.enter("PRINT -4")
        self.assertEqual(b.output(), " 5 \nA 5 B\n-4 \n")

    def test_loop_and_goto(self):
        b = prog("10 FOR I=1 TO 5", "20 S=S+I", "30 NEXT I", "40 PRINT S")
        b.enter("RUN")
        self.assertEqual(b.output(), " 15 \n")

    def test_gosub_if_and_edit(self):
        b = prog("10 N=3", "20 GOSUB 100", "30 PRINT R", "40 END", "100 R=1", "110 IF N=0 THEN RETURN",
                 "120 R=R*N", "130 N=N-1", "140 GOTO 110")
        b.enter("RUN")
        self.assertEqual(b.output(), " 6 \n")
        b.enter("30 PRINT R+1"); b.enter("RUN")
        self.assertTrue(b.output().endswith(" 7 \n"))
        b.enter("40")                            # delete END: execution falls into the subroutine
        with self.assertRaises(BasicError): b.enter("RUN")
        self.assertIn("RETURN WITHOUT GOSUB", b.output())
        self.assertIn("deleted", b.w.reasons.values()); self.assertIn("replaced", b.w.reasons.values())

    def test_two_char_variable_names(self):
        b = prog("10 COUNT=5", "20 COUNTER=9", "30 PRINT COUNT")
        b.enter("RUN")
        self.assertEqual(b.output(), " 9 \n")

    def test_strings_arrays_data(self):
        b = prog('10 A$="HELLO"', "20 B$=LEFT$(A$,2)+RIGHT$(A$,2)", "30 PRINT B$;LEN(A$)",
                 "40 DIM X(3)", "50 FOR I=0 TO 3:X(I)=I*I:NEXT I", "60 PRINT X(3)",
                 "70 READ P,Q", "80 PRINT P+Q", "90 DATA 4,5")
        b.enter("RUN")
        self.assertEqual(b.output(), "HELO 5 \n 9 \n 9 \n")

    def test_errors(self):
        for line, msg in (("10 PRINT 1/0", "DIVISION BY ZERO"), ("10 GOTO 99", "UNDEF'D STATEMENT"),
                          ('10 A=1:A$=2', "TYPE MISMATCH"), ("10 RETURN", "RETURN WITHOUT GOSUB"),
                          ("10 PRINT (", "SYNTAX"), ("10 READ A", "OUT OF DATA")):
            b = prog(line)
            with self.assertRaises(BasicError): b.enter("RUN")
            self.assertIn(msg, b.output())

    def test_poke_peek(self):
        b = prog("10 POKE 1024,1", "20 POKE 1024,PEEK(1024)+1", "30 PRINT PEEK(1024)")
        b.enter("RUN")
        self.assertEqual(b.output(), " 2 \n")
        self.assertEqual(len([i for i in b.w.spheres.values() if i.tag == "mem"]), 2)

    def test_save_load_and_directory(self):
        b = prog("10 PRINT 42"); b.enter('SAVE "ANSWER",8')
        b.enter("NEW"); self.assertEqual(b.numbers(), [])
        b.enter('LOAD "ANSWER",8'); b.enter("RUN")
        self.assertEqual(b.output(), " 42 \n")
        b.enter('LOAD "$",8'); b.enter("LIST")
        self.assertIn('"ANSWER" PRG', b.output())
        b.enter('LOAD "AN*",8'); self.assertEqual(b.numbers(), [10])
        with self.assertRaises(BasicError): b.enter('LOAD "MISSING",8')
        with self.assertRaises(BasicError): b.enter('LOAD "ANSWER"')       # default device 1: no datasette
        with self.assertRaises(BasicError): b.enter('SAVE "ANSWER",8')     # FILE EXISTS
        b.enter('SAVE "@0:ANSWER",8')
        self.assertIn("replaced", b.w.reasons.values())

    def test_loaded_lines_are_coupled_to_file(self):
        b = prog("10 PRINT 1"); b.enter('SAVE "P",8'); b.enter("NEW"); b.enter('LOAD "P",8')
        i = b.w.view.last_key("line", 10)
        self.assertEqual(b.w.spheres[b.w.spheres[i].deps[0]].tag, "file")

    def test_input_consumed_once(self):
        b = prog('10 INPUT "NAME";N$', "20 PRINT N$", inputs=["BOB"])
        b.enter("RUN")
        self.assertIn("BOB", b.output())
        self.assertEqual(b.w.view.count("basic.in"), 0)

    def test_runaway_stopped_and_replay(self):
        b = prog("10 GOTO 10", max_steps=500)
        with self.assertRaises(BasicError): b.enter("RUN")
        self.assertTrue(b.w.verify())

if __name__ == "__main__":
    unittest.main()
