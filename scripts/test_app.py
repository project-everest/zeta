""" Test the app.py functionality """

import unittest
import app_parse

class TestFuncParamsParse(unittest.TestCase):

    def test_param_parse(self):
        ps = 'uint64 x'
        t,n = app_parse.parse_func_param(ps)
        self.assertEqual(n, 'x')
        self.assertEqual(t, 'uint64')

    def test_param_parse_space(self):
        # add extra whitespaces
        ps = '   uint64   x    '
        t,n = app_parse.parse_func_param(ps)
        self.assertEqual(n, 'x')
        self.assertEqual(t, 'uint64')

    def test_param_parse_multiline(self):
        # add extra whitespaces
        ps = '''   uint64
x    '''
        t,n = app_parse.parse_func_param(ps)
        self.assertEqual(n, 'x')
        self.assertEqual(t, 'uint64')

    def test_params_parse(self):
        pstr = 'uint64 x, uint64 y'
        ps = app_parse.parse_func_params(pstr)
        self.assertEqual(len(ps), 2)
        self.assertEqual(('uint64','x'), ps[0])
        self.assertEqual(('uint64','y'), ps[1])

    def test_params_parse_multiline(self):
        pstr = '''uint64 x   ,
                  uint64   y'''
        ps = app_parse.parse_func_params(pstr)
        self.assertEqual(len(ps), 2)
        self.assertEqual(('uint64','x'), ps[0])
        self.assertEqual(('uint64','y'), ps[1])

    def test_parse_func(self):
        fstr = '''
/* some function */
int func (int x,
          app_key y,
          int z)
{
    return 0;
}

'''
        fn = app_parse.parse_func(fstr)
        self.assertEqual(fn.name, 'func')
        self.assertEqual(len(fn.params), 3)
        self.assertEqual(fn.output, 'int')

if __name__ == '__main__':
    unittest.main()
