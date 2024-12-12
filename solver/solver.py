import os
from z3 import *

class SemGusSolver:
    def __init__(self, grammar, semantics, specification, functions, synth_fun, max_size = 4):
        self.grammar = grammar
        self.semantics = semantics
        self.specification = specification
        self.max_size = max_size
        self.functions = functions
        self.synth_fun = synth_fun
        self.solver = Solver()

    def linear_encoding(self):
        """
        Encodes the problem into a linear format using Z3.
        """

        # Max size of program
        L = self.max_size

        # Max arity of Program
        K = 0

        # Max number of nonterminals
        N = 0

        # Max number of productions

        # Maps each nonterminal to an index
        nts = {}

        # Maps each nonterminal production to an index and
        # seperates them by dicts by nonterminal
        nt_prods = []
        
        # Single dict maps prods to indices
        production_mappings = {}

        # Tracks nonterminals of children of each production
        children = {}

        # Number of productions
        num_prods = 0

        # Tracks variables of each nonterminal and their types 
        funcs = self.functions

        # Specifies the input, output, and term variables of each nonterminal
        symbols = {}

        # Tracks each constraint type and variables involved for each chc
        chcs = {}

        # Behovioral specification with input/output examples
        examples = []

        # Mapppings of each variable to their example
        ex_vars = []

        # Fill various data structures
        for nonterminal, production in self.grammar.items():
            nts[nonterminal] = N
            N += 1
            prods = {}
            for i in production['constructors']:
                prods[i['name']] = num_prods
                children[i['name']] = i['children']
                if K < len(i['children']):
                    K = len(i['children'])
                num_prods += 1
            nt_prods.append(prods)

        for n in nt_prods:
            for key, value in n.items():
                production_mappings[key] = value

        for id, chc in self.semantics.items():
            start = id.find('-') + 1
            end = id.find('-',start)
            chc_id = id[start:end]
            name = chc["head"]["name"]
            symbols[name] = {}
            symbols[name]["inputs"] = []
            symbols[name]["outputs"] = []
            for i in chc["symbols"]["inputs"]:
                symbols[name]["inputs"].append(i["id"])
            for i in chc["symbols"]["outputs"]:
                symbols[name]["outputs"].append(i["id"])
            symbols[name]["term"] = chc["symbols"]["term"]["id"]
            args = []

            for i in chc["constraint"]["arguments"]:
                if isinstance(i,dict):
                    if ("$" + i["name"]) in children:
                        if len(children[("$"+i["name"])]) > 0:
                            sub_args = []
                            for j in i["arguments"]:
                                if isinstance(j,dict):
                                    sub_args.append(j["name"])
                                else: sub_args.append(j)
                            args.append((i["name"], sub_args))
                        else:
                            args.append(i["name"])
                    else:
                        args.append(i["name"])
                else:
                    args.append(i)
            if chc_id in chcs:
                body_rels = {}
                for i in chc["bodyRelations"]:
                    body_rels[i["arguments"][0]] = i["signature"][0]
                args.append((body_rels,chc["constructor"]["arguments"]))
                chcs[chc_id]=("ite",args)
            else:
                chcs[chc_id]=(chc["constraint"]["name"],args)

        for i in self.specification:
            args = []
            for j in i["arguments"]:
                if isinstance(j,dict):
                    args.append(j["name"])
                else:
                    args.append(j)
            examples.append((i["name"],args))

        for i in examples:
            var_mappings = {}
            var = 0 
            for vars, _ in funcs[i[0]].items():
                var_mappings[vars] = i[1][var]
                var += 1
            ex_vars.append(var_mappings)

        P = len(production_mappings)
        
        # Uninterpreted function: n_l maps statement lines to nonterminal identifiers
        # Domain: [0..D-1], Range: [0..N-1]
        n_l = Function('n_l', IntSort(), IntSort())

        # Uninterpreted function: p_l maps statement lines to production identifiers
        # Domain: [0..L-1], Range: [0..<number of productions>-1] (use the production count as needed)
        p_l = Function('p_l', IntSort(), IntSort())

        # Uninterpreted function: c maps line l and child ID k to corresponding line
        # Domain: [0..L-1] x [0..K-1], Range: [0..L-1]
        c = Function('c', IntSort(), IntSort(), IntSort())

        # Uninterpreted function: v_e_l maps example and line l to a value in the domain of V_al
        # Domain: [0..E-1] x [0..L-1], Range: appropriate domain for values (here using Int as an example)
        v_e_l = Function('v_e_l', IntSort(), IntSort(), IntSort())

        # S is the starting nonterminal
        S = nts[self.synth_fun["termType"]]

        # List which holds constraints
        constraints = []

        # Uninterpreted function constraints
        
        # Constraints on n_l
        for l in range(L):
            constraints.append(And(n_l(l) >= 0, n_l(l) < N))

        # Constraints on p_l
        for l in range(L):
            constraints.append(And(p_l(l) >= 0, p_l(l) < P))  # Replace N with the number of productions

        # Constraints on c
        for l in range(L):
            for k in range(K):
                constraints.append(And(c(l, k) >= 0, c(l, k) < L))

        # Constraints on v_e_l
        for e in range(len(examples)):
            for l in range(L):
                constraints.append(v_e_l(e,l) >= 0)  # Depends on value domain
        
        
        # Structural Constraints
        
        # Encoding: n_l(L-1) = S; last line is starting nonterminal
        constraints.append(n_l(L - 1) == S)

        # Encoding: Assigns each child to appropriate nonterminal and lower line than parent
        for i in range(L):
            for production, child in children.items():
                child_constraints = []
                for child_idx, ch in enumerate(child):
                    child_constraints.append(n_l(c(i,child_idx)) == nts[ch])
                    child_constraints.append(c(i,child_idx) < i)
                if len(child_constraints) != 0:
                    constraints.append(
                        Implies(p_l(i) == production_mappings[production],And(*child_constraints))
                    )

            # Encoding: Ensures consistency between nonterminal and production for each line
            for nt in range(len(nt_prods)):
                constraints.append(
                    Implies(n_l(i) == nt, Or([p_l(i) == p for _, p in nt_prods[nt].items()]))
                )

        # Behavioral Constraints

        # Function that enacts operations on children
        def op(production, children_values, vars, example, line):
            for prod, rule in chcs.items():
                nonterm = 0
                for i in range(len(nt_prods)):
                    for p in nt_prods[i]:
                        if prod == p:
                            nonterm = i
                for n, i in nts.items():
                    if i == nonterm:
                        nonterm = n
                rule_name = nonterm + ".Sem"
                inputs = symbols[rule_name]["inputs"]
                output = symbols[rule_name]["outputs"][0]

                if production == prod:
                    if rule[0] == '=':
                        if rule[1][0] == output and rule[1][1] in inputs:
                            return v_e_l(example, line) == vars[rule[1][1]]
                        elif rule[1][0] == output and isinstance(rule[1][1],int):
                            return v_e_l(example, line) == rule[1][1]
                        elif rule[1][0] == output and rule[1][1] == 'false':
                            return v_e_l(example, line) == 0
                        elif rule[1][0] == output and rule[1][1] == 'true':
                            return v_e_l(example, line) == 1
                        elif rule[1][0] == output and isinstance(rule[1][1],tuple):
                            embedded_rule = rule[1][1]
                            if embedded_rule[0] == '+':
                                return v_e_l(example, line) == v_e_l(example,c(children_values[0][0],children_values[0][1])) + v_e_l(example,c(children_values[1][0],children_values[1][1]))
                            if embedded_rule[0] == '-':
                                return v_e_l(example, line) == v_e_l(example,c(children_values[0][0],children_values[0][1])) - v_e_l(example,c(children_values[1][0],children_values[1][1]))
                            if embedded_rule[0] == '*':
                                return v_e_l(example, line) == v_e_l(example,c(children_values[0][0],children_values[0][1])) * v_e_l(example,c(children_values[1][0],children_values[1][1]))
                            if embedded_rule[0] == '/':
                                return v_e_l(example, line) == v_e_l(example,c(children_values[0][0],children_values[0][1])) / v_e_l(example,c(children_values[1][0],children_values[1][1]))
                            if embedded_rule[0] == '<':
                                return If(v_e_l(example,c(children_values[0][0],children_values[0][1])) < v_e_l(example,c(children_values[1][0],children_values[1][1])),v_e_l(example, line) == 1,v_e_l(example, line) == 0)
                            if embedded_rule[0] == '>':
                                return If(v_e_l(example,c(children_values[0][0],children_values[0][1])) > v_e_l(example,c(children_values[1][0],children_values[1][1])),v_e_l(example, line) == 1,v_e_l(example, line) == 0)
                            if embedded_rule[0] == '==':
                                return If(v_e_l(example,c(children_values[0][0],children_values[0][1])) == v_e_l(example,c(children_values[1][0],children_values[1][1])),v_e_l(example, line) == 1,v_e_l(example, line) == 0)
                            if embedded_rule[0] == 'not':
                                return If(Not(v_e_l(example,c(children_values[0][0],children_values[0][1])) == 1), v_e_l(example, line) == 1, v_e_l(example, line) == 0)
                            if embedded_rule[0] == 'and':
                                If(And(v_e_l(example,c(children_values[0][0],children_values[0][1])) == 1,v_e_l(example,c(children_values[1][0],children_values[1][1])) == 1),v_e_l(example, line) == 1,v_e_l(example, line) == 0)
                    elif rule[0] == 'ite':
                        return If(v_e_l(example,c(children_values[0][0],children_values[0][1])) == 1, v_e_l(example, line) == v_e_l(example,c(children_values[1][0],children_values[1][1])), v_e_l(example, line) == v_e_l(example,c(children_values[2][0],children_values[2][1]))) 
            return True

        for i in range(len(examples)):
            output_var = symbols[examples[i][0]]["outputs"][0]
            output = ex_vars[i][output_var]
            constraints.append(v_e_l(i,L - 1) == output)

            for j in range(L):
                for production, child in children.items():
                    children_values = []
                    for child_idx, ch in enumerate(child):
                        children_values.append((j,child_idx))

                    constraints.append(
                        Implies(p_l(j) == production_mappings[production],op(production, children_values,ex_vars[i],i,j))
                    )

        for x in constraints:
            self.solver.add(x)
        
        result = self.solver.check()

        def build_program(model, l):
            index = model.eval(p_l(l))
            prod = next((k for k, v in production_mappings.items() if v == index), None)
            if (len(children[prod]) == 0):
                return " " + str(prod[1:]) + " "
            else:
                program = str(prod[1:]) + " ( "
                for i in range(len(children[prod])):
                    child_index = model.eval(c(l,i))
                    program += build_program(model, child_index)
                program += " ) "
                return program

        if result == "unsat":
            print("No Solution")
        else:
            print("Solution found:")
            model = self.solver.model()
            #for var in model:
            #    print(f"{var}: {model[var]}")
            print(build_program(model, L-1))


    def solve(self):
        """
        Solves the problem and prints results.
        """

        print("Encoding problem...")
        self.linear_encoding()

