import re

class Matrix:
    def __init__(self, matrix):
        self.Matrix = matrix
    
    def copy_submatrix(self, row_start, row_end, col_start, col_end):
        sub_matrix = [['']*(col_end - col_start) for i in range(row_end - row_start)]
        
        for i in range(0, row_end - row_start):
            for j in range(0, col_end - col_start):
                sub_matrix[i][j] = matrix[row_start + i][col_start + j]
        return sub_matrix
    
    def calculate_closure(self, sub_matrix):
        n = len(sub_matrix)
        if n == 1:
            return
        
        upper_left_matrix = self.copy_submatrix(sub_matrix, 0, n/2, 0, n/2)
        bottom_right_matrix = self.copy_submatrix(sub_matrix, n/2, n, n/2, n)
        
        self.calculate_closure(upper_left_matrix)
        self.calculate_closure(bottom_right_matrix)
        
    def partition_3(matrix):
        if len(matrix) < 3:
            return;
      #lemma(p, 2*n/3)
    
    def partition_4(matrix):
        if len(matrix) < 4:
            return;
      #lemma(p, 3*n/4)

class CFG():
    def __init__(self, **kwargs):
        self.NonTerminals = kwargs.get('NonTerminals', set())
        self.Terminals = kwargs.get('Terminals', set())
        self.Definitions = kwargs.get('Definitions', dict())
        self.S = kwargs.get('S', str())
        self.delimiter = kwargs.get('delimiter', ' ')
        self.epsilon = kwargs.get('epsilon', 'ε')

    def copy(self):
        res_prod = dict()
        for key, value in self.Definitions.items():
            res_prod[key] = value.copy()

        new_cfg = CFG(NonTerminals=self.NonTerminals.copy(), Terminals=self.Terminals.copy(), Definitions=res_prod, S=self.S)
        return new_cfg

    def get_rule(self, var):
        return self.Definitions.get(var, set())

    def union_rule(self, var, rule_set):
        for rule in rule_set:
            self.add_rule(var, rule)

    def add_rule(self, var, rule):
        self.NonTerminals.add(var)

        for c in rule.split(self.delimiter):
            if c not in self.Terminals and c != self.epsilon:
                self.NonTerminals.add(c)

        if var not in self.Definitions:
            self.Definitions[var] = set()
        self.Definitions[var].add(rule)

    def remove_rule(self, var, rule):
        self.Definitions.get(var, set()).discard(rule)

        tmp = rule.split(self.delimiter)
        tmp.append(var)
        for c in tmp:
            if c in self.NonTerminals:
                if len(self.Definitions.get(c, set())) == 0:
                    self.NonTerminals.discard(c)
                    self.Definitions.pop(c, None)

    def remove_var(self, var):
        for rule in self.get_rule(var).copy():
            self.remove_rule(var, rule)

        for tmp_var in self.NonTerminals.copy():
            for rule in self.get_rule(tmp_var).copy():
                for c in rule.split(self.delimiter):
                    if c == var:
                        self.remove_rule(var, rule)

    # step - 1: Eliminate the start symbol from right-hand sides
    def add_start_symbol(self):
        res = self.copy()
        res.add_rule('S0', 'S')
        res.S = 'S0'
        return res

    # Eliminate rules with terminals and non-terminals
    def remove_nonsolitary_terminals(self):
        res = self.copy()
        sub = dict()
        for c in res.Terminals:
            sub[c] = 'C'+c

        for var in res.NonTerminals.copy():
            for rule in res.get_rule(var).copy():
                rule = rule.split(res.delimiter)

                if len(rule) > 1:
                    for i in range(len(rule)):
                        c = rule[i]
                        if c in res.Terminals:
                            res.remove_rule(var, res.delimiter.join(rule))
                            res.add_rule(sub[c], c)
                            c = sub[c]
                        rule[i] = c
                    res.add_rule(var, res.delimiter.join(rule))
        return res

    # Eliminate right-hand sides with more than 2 nonterminals
    def remove_multiple_terminals(self):
        res = self.copy()
        count = 1
        for var in res.NonTerminals.copy():
            for rule in res.get_rule(var).copy():
                rule = rule.split(res.delimiter)

                if len(rule) > 2 and set(rule).issubset(res.NonTerminals):
                    res.remove_rule(var, res.delimiter.join(rule))
                    tmp = rule

                    v = 'C'+str(count)
                    count += 1
                    res.add_rule(var, tmp.pop(0) + res.delimiter + v)

                    while len(tmp) > 2:
                        pre_v = v
                        v = 'C'+str(count)
                        count += 1
                        res.add_rule(pre_v, pre_v+res.delimiter + tmp.pop(0))
                    res.add_rule(v, res.delimiter.join(tmp))
        return res

    # Eliminate null-rules
    def epsilon_ommit(self, nullable, rule):
        if len(self.delimiter.join(rule)) == 1:
            return set([rule])

        res = set([rule])
        for c in rule.split(self.delimiter):
            if c in nullable:
                tmp = rule.split(self.delimiter)
                tmp.remove(c)
                res_tmp = self.epsilon_ommit(
                    nullable, self.delimiter.join(tmp))
                # print("epsion_ommit recur: {}".format(res_tmp))
                res = res.union(res_tmp)
        return res

    def eliminate_null_rule(self):
        res = self.copy()
        nullable = set()
        stop = False

        while stop == False:
            stop = True

            for var in res.NonTerminals:
                if var not in nullable and var != res.S:
                    for rule in res.get_rule(var):
                        rule = rule.split(res.delimiter)

                        if len(rule) == 1 and res.delimiter.join(rule) == res.epsilon:
                            nullable.add(var)
                            stop = False
                        elif set(rule).issubset(res.NonTerminals) and set(rule).issubset(nullable):
                            nullable.add(var)
                            stop = False

        if len(nullable) > 0:
            for var in nullable:
                res.remove_rule(var, res.epsilon)

            for var in res.NonTerminals.copy():
                for rule in res.get_rule(var).copy():
                    for c in nullable:
                        if c in rule.split(res.delimiter):
                            ommited = res.epsilon_ommit(nullable, rule)
                            # print(ommited)
                            res.union_rule(var, ommited)
        return res

    # Eliminate eliminate_unit_rule rules
    def eliminate_unit_rule(self):
        res = self.copy()
        stop = False
        while stop == False:
            stop = True

            for var in res.NonTerminals.copy():
                for rule in res.get_rule(var).copy():
                    rule = rule.split(res.delimiter)

                    if len(rule) == 1:
                        tmp = res.delimiter.join(rule)

                        if tmp in res.NonTerminals:
                            stop = False
                            res.union_rule(var, res.get_rule(tmp))
                            res.remove_rule(var, tmp)
                            res.remove_rule(var, var)
        return res

    def is_CNF(self):
        for var in self.NonTerminals:
            for rule in self.get_rule(var):
                rule = rule.split(self.delimiter)
                if len(rule) > 2:
                    return False
                elif len(rule) == 2:
                    if not set(rule).issubset(self.NonTerminals):
                        return False
                else:
                    if not set(rule).issubset(self.Terminals):
                        return False
        return True

    def CNF(self):
        if self.is_CNF():
            return self
        return self.add_start_symbol().remove_nonsolitary_terminals().remove_multiple_terminals().eliminate_null_rule().eliminate_unit_rule()

    def __str__(self):
        def_str = ''
        for key, value in self.Definitions.items():
            def_str += "\n\t\t{}\t->\t{}".format(key, "\t| ".join(value))

        return "\nG(NonTerminals, Terminals, Definitions, Start):\n\tNonTerminals={}\n\tTerminals={}\n\Definitions={}\n\tStart={}".format(
            self.NonTerminals,
            self.Terminals,
            def_str,
            self.S
        )


def main():
    input_grammar = {
    "<grammar>" : '"{" <defs> "}" | "{" "}"',
    "<defs>" : "<def> <defs> | <def>",
    "<def>" : "<key> ':' '[' <rules> ']'",
    "<key>" : "'\"' '<' [a-zA-Z0-9]+ '>' '\"'",
    "<rules>" : "<rule> <rules>| <rule>",
    "<rule>" : "'[' <sym> ',' <rule> ']' |  '[' ']'",
    "<sym>" : "<key> | '"' [a-zA-Z0-9]+ '"'"
    }
    start_symbol = "<grammar>"
    terminals = set()
    non_terminals = set(input_grammar.keys())
    updated_definition = dict()

    for key,value in input_grammar.items():
        definitions = value.split("|")
        for definition in definitions:
            terms = definition.split(" ")
            for term in terms:
                if len(term) > 0 and term not in input_grammar.keys():
                    terminals.add(term)
        updated_definition[key] = set(definitions)

    cfg = CFG(NonTerminals=non_terminals, Terminals=terminals, Definitions=updated_definition, S="<grammar>")
    return(cfg.CNF())


if __name__ == "__main__":
    cnf_formatted_grammar = main()
    print(cnf_formatted_grammar)

    parse_string = "d<f"
    string_len = len(parse_string)
    
    min_size = string_len + 1;
    actual_size = 1;
    while actual_size < min_size:
        actual_size *= 2

    matrix = [[0]*(actual_size) for i in range(actual_size)]
    non_terminals = list(cnf_formatted_grammar.Definitions.keys())
    terminals = list(cnf_formatted_grammar.Definitions.values())
    
    # for i in range(0, string_len):
    #     for term in cnf_formatted_grammar.Terminals:
    #         regex = f'{term}'            
    #         match = re.search(regex, f"'{parse_string[i]}'")
    #         if match is not None:
    #             for nt in non_terminals:
    #                 terminal_per_production = list(cnf_formatted_grammar.Definitions[nt])
    #                 if len(terminal_per_production) == 1 and term == terminal_per_production[0]:
    #                     matrix[i][i+1] = nt
    #                     break
    #             break

    # print(matrix)
    # mtx = Matrix(matrix)
    # n = len(matrix)
    # print(mtx.copy_submatrix(0, n//2, 0, n//2))
