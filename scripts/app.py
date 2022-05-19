""" Classes related to a Zeta application """

class StateFn:
    """
    A state transition function of the Zeta state machine.

    Attributes:
        name: name of the function
        params: non-record input parameters
    """
    def __init__ (self, name, params, output, body):
        self.name = name
        self.params = params
        self.body = body
        self.output = output

    def gen_verifier_code (self):
        """
        Return a string C definition of the function
        """
        pass

    def everparse_param_name (self):
        return f"{self.name}_param"

    def gen_everparse_param_type (self):
        """
        Return a string that represents the parameter type of the function in everparse
        """
        s = "struct {\n"

        for (t,n) in self.params:
            # Transform app_record parameters to slot params
            if t == 'app_record':
                t = 'slot'
                n = f's_{n}'

            s += f'  {t} {n};\n'

        s += f'}} {self.everparse_param_name()};\n'

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

def gen_everparse_types (app):
    """
    Generate the text with everparse definitions for the app
    """

    # carry over the type definitions specified in the app
    s = '/* Application specified types */\n'
    s += app.type_defs + "\n"

    # add the type definition for a slot
    s += '/* Slot type */\n'
    s += 'uint16 slot;\n\n'

    # add type defs for state transition functions
    s += '/* Application state transition function parameter types */\n'
    for f in app.fn_defs:
        s += f.gen_everparse_param_type() + '\n'
    return s
