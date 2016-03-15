import json
import argparse
import traceback


PRIORITIES = {
    "~": 5,
    "D": 5,
    "B": 5,
    "&": 4,
    "|": 3,
    "=>": 2,
    "<=>": 1,
    "(": 0,
    ")": 0
}

ASSOCIATIVITIES = {
    "~": "R",
    "D": "R",
    "B": "R",
    "&": "L",
    "|": "L",
    "=>": "L",
    "<=>": "L"
}


def postfix(formula):
    operators_stack = []
    postfix_formula = []
    formula_length = len(formula)
    i = 0
    diamond_or_box = None
    while i < formula_length:
        op = formula[i]
        i += 1
        if op == " ":
            continue
        #print op, operators_stack, postfix_formula
        # special case
        ###########################################
        if diamond_or_box is not None:
            brackets = 0
            operand = op
            if op == "(":
                brackets += 1
            while i < len(formula):
                op = formula[i]
                i += 1
                if op == " ":
                    continue

                if op == "(":
                    brackets += 1
                    operand += op
                    continue
                elif op == ")":
                    brackets -= 1
                    if brackets < 0:
                        break
                    operand += op
                    continue

                if op == "<":
                    op += formula[i] + formula[i+1]
                    i += 2
                elif op == "=":
                    op += formula[i]
                    i += 1

                if op in PRIORITIES and PRIORITIES[op] < PRIORITIES[diamond_or_box] and brackets == 0:
                    break

                operand += op

            diamond_or_box = None
            postfix_formula.append(operand)

            if i == len(formula):
                break
        ###########################################

        if op == "<":
            op += formula[i] + formula[i+1]
            i += 2
        elif op == "=":
            op += formula[i]
            i += 1

        # special case
        ############################
        if op == "D":
            diamond_or_box = "D"
        elif op == "B":
            diamond_or_box = "B"
        ############################

        if op not in PRIORITIES:
            # print op, operators_stack, postfix_formula
            postfix_formula.append(op)
        elif op == "(":
            operators_stack.append(op)
        elif op == ")":
            top = operators_stack.pop()

            while top != "(":
                postfix_formula.append(top)
                top = operators_stack.pop()
        else:
            # print op, PRIORITIES[op], operators_stack, postfix_formula
            if len(operators_stack) == 0:
                operators_stack.append(op)
                continue

            while len(operators_stack) > 0 and PRIORITIES[operators_stack[-1]] >= PRIORITIES[op]:
                if PRIORITIES[operators_stack[-1]] == PRIORITIES[op] and ASSOCIATIVITIES[op] == "R":
                    break
                top = operators_stack.pop()
                postfix_formula.append(top)
            operators_stack.append(op)

    while len(operators_stack) > 0:
        top = operators_stack.pop()
        postfix_formula.append(top)

    return postfix_formula


def ev_op(w, kripke_structure, operand):
    if operand == "T":
        return True
    elif operand == "F":
        return False

    if operand in kripke_structure["labels"][w]:
        return True
    return False


def box(w, kripke_structure, operand, level):
    result = True

    #print "%scheck if %s satisfy B%s" % ("|\t" * (level), w, str(operand))
    for neigh in kripke_structure["relations"][w]:
        res_add = evaluate(neigh, kripke_structure, operand, level+1)
        result *= res_add

    return result > 0


def diamond(w, kripke_structure, operand, level):
    result = False
    #print "%scheck if %s satisfy D%s" % ("|\t" * (level), w, str(operand))

    for neigh in kripke_structure["relations"][w]:
        res_add = evaluate(neigh, kripke_structure, operand, level+1)
        result += res_add
    return result > 0


def evaluate(w, kripke_structure, expression, level):
    postfix_expression = postfix(expression)
    operands_stack = []

    if w not in kripke_structure["worlds"]:
        raise Exception("%s not a world" % w)

    print "%scheck if %s satisfy %s" % ("|\t" * level, w, str(expression))

    for i in range(len(postfix_expression)):
        op = postfix_expression[i]

        if op not in PRIORITIES:
            if i < len(postfix_expression) - 1 and postfix_expression[i+1] in ["D", "B"]:
                operands_stack.append(op)
                continue

            res = ev_op(w, kripke_structure, op)

            if res is True:
                print "%s%s satisfy %s" % ("|\t" * (level + 1), w, op)
            else:
                print "%s%s not satisfy %s" % ("|\t" * (level + 1), w, op)

            operands_stack.append(res)
        if op == "D":
            operand1 = operands_stack.pop()
            res = diamond(w, kripke_structure, operand1, level)
            operands_stack.append(res)
            print "%s-%s" % ("|\t" * (level), str(res))
            #print "%s%s" % ("|\t" * (level) + "|-", res)
        elif op == "B":
            operand1 = operands_stack.pop()
            res = box(w, kripke_structure, operand1, level)
            operands_stack.append(res)
            print "%s-%s" % ("|\t" * (level), str(res))
            #print "%s%s" % ("|\t" * (level) + "|-", res)
        elif op == "&":
            operand2 = operands_stack.pop()
            operand1 = operands_stack.pop()

            res = operand1 * operand2 > 0
            operands_stack.append(res)
            print "%s-%s" % ("|\t" * (level), str(res))
            #print "%sevaluating... \t%s %s %s = %s" % ("|\t" * (level + 1), str(operand1), str(op), str(operand2), str(res))
        elif op == "|":
            operand2 = operands_stack.pop()
            operand1 = operands_stack.pop()

            res = (operand1 + operand2) > 0
            operands_stack.append(res)
            print "%s-%s" % ("|\t" * (level), str(res))
            #print "%sevaluating... \t%s %s %s = %s" % ("|\t" * (level + 1), str(operand1), str(op), str(operand2), str(res))
        elif op == "~":
            operand1 = operands_stack.pop()

            res = not operand1
            operands_stack.append(res)
            print "%s-%s" % ("|\t" * (level), str(res))
            #print "%sevaluating... \t%s%s = %s" % ("|\t" * (level + 1), str(op), str(operand1), str(res))
        elif op == "=>":
            operand2 = operands_stack.pop()
            operand1 = operands_stack.pop()

            res = not operand1 or operand2
            operands_stack.append(res)
            print "%s-%s" % ("|\t" * (level), str(res))
            # print "%s$%s: %s, %s$" % ("|\t" * (level + 1), op, str(operand1), str(operand2))
            #print "%sevaluating... \t%s %s %s = %s" % ("|\t" * (level + 1), str(operand1), str(op), str(operand2), str(res))
        elif op == "<=>":
            operand2 = operands_stack.pop()
            operand1 = operands_stack.pop()

            # print "%s$%s: %s, %s$" % ("|\t" * (level + 1), op, str(operand1), str(operand2))

            result = False
            if (operand1 is True and operand2 is True) or (operand1 is False and operand2 is False):
                result = True

            operands_stack.append(result)
            print "%s-%s" % ("|\t" * (level), str(res))
            #print "%sevaluating... \t%s %s %s = %s" % ("|\t" * (level + 1), str(operand1), str(op), str(operand2), str(res))

    #print "%s%s" % ("|\t" * level + "|-", operands_stack[0])
    return operands_stack[0]


def read_kripke_file(kripke_file):
    try:
        fd = open(kripke_file, "r")
        kripke_structure = json.load(fd)
        fd.close()
    except:
        print traceback.format_exc()
        return None

    return kripke_structure


def read_formulas_file(formulas_file):
    try:
        fd = open(formulas_file, "r")
        lines = fd.readlines()
        fd.close()
    except:
        print traceback.format_exc()
        return None

    formulas = []
    for line in lines:
        if line == "\n" or line == " ":
            continue
        line = line.split("|=")
        formula = {}
        formula["world"] = line[0].lstrip(" ").rstrip(" ")
        formula["formula"] = line[1].lstrip(" ").rstrip(" \n")
        formulas.append(formula)

    return formulas


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("kripke_file")
    parser.add_argument("formulas_file")

    args = parser.parse_args()
    kripke_file = args.kripke_file
    formulas_file = args.formulas_file

    kripke_structure = read_kripke_file(kripke_file)
    formulas = read_formulas_file(formulas_file)

    for formula in formulas:
        print "Formula: %s" % formula
        print "-------------------------------"
        try:
            # print "CHECKING FORMULA: %s satisfy %s" % (formula["world"], formula["formula"])
            evaluate(formula["world"], kripke_structure, formula["formula"], 0)
        except:
            print traceback.format_exc()
            print "Invalid expression!"
        print "-------------------------------\n"


    # # args = parser.parse_args()
    # # postfix_expression = postfix("3 + 4 * 2 / ( 1 - 5 ) ^ 2 ^ 3")
    # # expression = "((x | y) & z) <=> x => y | z & y"
    # # postfix_expression = postfix(expression)
    # # print postfix_expression

    # #expression = "a & b | DDB(a & DBb)Ea & b => a"
    # expression1 = "B~p & BB~p"
    # # expression2 = "DD(p&q) & D T"
    # # expression2 = "BD~q"
    # # expression2 = "DD(p&q) & ~D T => DD q"
    # expression2 = "~Dp & ~D~(q&p) | ~p & q"
    # w = "a"
    # # expression2 = "~p&~p~~~"
    # kripke_structure = read_kripke_file("input_file")
    # print "check if %s satisfy %s" % (w, expression2)
    # try:
    #     evaluate(w, kripke_structure, expression2, 0)
    # except:
    #     print traceback.format_exc()
    #     print "Invalid expression!"
    # #print evaluate(postfix_expression)
