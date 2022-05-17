""" Classes related to a Zeta application """

class StateFn:
    """
    A state transition function of the Zeta state machine.

    Attributes:
        name: name of the function
        arity: number of input/output records
        params: non-record input parameters
    """
    def __init__ (self, name, arity, params, output, body):
        self.name = name
        self.arity = arity
        self.params = params
        self.body = body
        self.output = output

    def gen_verifier_code (self):
        """
        Return a string C definition of the function
        """
        pass

    def gen_everparse_param_type (self):
        """
        Return a string that represents the parameter type of the function in everparse
        """

        s = "struct {\n"

        for p in self.params:
            s += "  " + p + ";\n"

        for sl in range(self.arity):
            s += "  slot _s" + str(sl) + ";\n";

        s += "} " + self.name + "_param;\n"

        return s

    def gen_host_decl (self):
        """
        Return a string C declaration of the class representing the function
        """
        pass

    def gen_host_def (self):
        pass

class App:
    """
    A zeta application
    """
    def __init__ (self, name, type_defs, fn_defs):

        self.name = name
        self.type_defs = type_defs
        self.fn_defs = fn_defs
