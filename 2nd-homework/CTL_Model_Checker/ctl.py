import json
import tarjan as tj
import argparse
import traceback
from copy import deepcopy


def exists_path(w, relations_sat, strongly_connected_component, visited, result):
    if len(result) > 0:
        return
    visited.append(w)
    for neigh in relations_sat[w]:
        if neigh not in visited:
            if neigh in strongly_connected_component:
                result.append(neigh)
            else:
                exists_path(neigh, relations_sat, strongly_connected_component, visited, result)


def eg(w, kripke_structure, expression, level):
    if evaluate(w, kripke_structure, expression, level + 1) is False:
        return False

    worlds_that_satisfies_expression = []
    for world in kripke_structure["worlds"]:
        if evaluate(world, kripke_structure, expression, level + 1) is True:
            worlds_that_satisfies_expression.append(world)

    relations_sat = deepcopy(kripke_structure["relations"])
    for world in relations_sat.keys():
        if world not in worlds_that_satisfies_expression:
            del relations_sat[world]
        else:
            for neigh in list(relations_sat[world]):
                if neigh not in worlds_that_satisfies_expression:
                    relations_sat[world].remove(neigh)

    strongly_connected_components = tj.tarjan(relations_sat)

    for strongly_connected_component in strongly_connected_components:
        if (len(strongly_connected_component) == 1
            and strongly_connected_component[0] not in relations_sat[strongly_connected_component[0]]):
            continue

        result = []
        exists_path(w, relations_sat, strongly_connected_component, [], result)
        if len(result) > 0:
            return True

    return False


def ex(w, kripke_structure, expression, level):
    for neigh in kripke_structure["relations"][w]:
        if evaluate(neigh, kripke_structure, expression, level + 1) is True:
            return True

    return False


def dfs(w, kripke_structure, f1, f2, visited, good_states, level):
    if len(good_states) > 0:
        return 1

    if w in visited:
        if w in good_states:
            return 1
        return 0

    visited.append(w)
    if evaluate(w, kripke_structure, f2, level + 1) is True:
        good_states.append(w)
        return 1

    if evaluate(w, kripke_structure, f1, level + 1) is False:
        return 0

    for neigh in kripke_structure["relations"][w]:
        if dfs(neigh, kripke_structure, f1, f2, visited, good_states, level + 1) is True:
            good_states.append(neigh)
            return 1

    return 0


def eu(w, kripke_structure, f1, f2, level):
    good_states = []
    visited = []

    dfs(w, kripke_structure, f1, f2, visited, good_states, level)

    return len(good_states) > 0


def ef(w, kripke_structure, expression, level):
    return eu(w, kripke_structure, "T", expression, level)


def ax(w, kripke_structure, expression, level):
    return not ex(w, kripke_structure, "~(%s)" % expression, level)


def ag(w, kripke_structure, expression, level):
    return not ef(w, kripke_structure, "~(%s)" % expression, level)


def af(w, kripke_structure, expression, level):
    return not eg(w, kripke_structure, "~(%s)" % expression, level)


def au(w, kripke_structure, f1, f2, level):
    return ((not eu(w, kripke_structure, "~(%s)" % f2, "~(|(%s, %s))" % (f1, f2), level)) and
            (not eg(w, kripke_structure, "~(%s)" % f2, level)))


def evaluate(w, kripke_structure, expression, level):
    print "%schecking if %s satisfy %s" % ("|\t" * (level), w, expression)

    splited_expression = expression.split("(", 1)
    op = splited_expression[0].rstrip(" ").lstrip(" \n")
    try:
        expression = splited_expression[1][:-1]
    except:
        pass
    if op.islower() or op in "TF":
        result = False
        if op == "T":
            result = True
        elif op == "F":
            result = False
        elif expression in kripke_structure["labels"][w]:
            result = True

        print "%s%s is %s in world %s" % ("|\t" * (level+1), op, str(result), w)
        return result
    elif op == "&":
        brackets = 0
        for i in range(len(expression)):
            if expression[i] == "," and brackets == 0:
                break
            if expression[i] == "(":
                brackets += 1
            elif expression[i] == ")":
                brackets -= 1

        operand1 = expression[0:i].lstrip(" ").rstrip(" \n")
        operand2 = expression[i+1:].lstrip(" ").rstrip(" \n")

        result = (evaluate(w, kripke_structure, operand1, level+1) * evaluate(w, kripke_structure, operand2, level+1)) > 0

        print "%s-%s" % ("|\t" * (level), str(result))
        #print "%s%s   &   \t%s   =   %s" % ("|\t" * (level), operand1, operand2, str(result))

        return result
    elif op == "|":
        brackets = 0
        for i in range(len(expression)):
            if expression[i] == "," and brackets == 0:
                break
            if expression[i] == "(":
                brackets += 1
            elif expression[i] == ")":
                brackets -= 1

        operand1 = expression[0:i].lstrip(" ").rstrip(" \n")
        operand2 = expression[i+1:].lstrip(" ").rstrip(" \n")

        result = (evaluate(w, kripke_structure, operand1, level+1) + evaluate(w, kripke_structure, operand2, level+1)) > 0

        print "%s-%s" % ("|\t" * (level), str(result))
        #print "%s%s   |   \t%s   =   %s" % ("|\t" * (level), operand1, operand2, str(result))

        return result
    elif op == "=>":
        brackets = 0
        for i in range(len(expression)):
            if expression[i] == "," and brackets == 0:
                break
            if expression[i] == "(":
                brackets += 1
            elif expression[i] == ")":
                brackets -= 1

        operand1 = expression[0:i].lstrip(" ").rstrip(" \n")
        operand2 = expression[i+1:].lstrip(" ").rstrip(" \n")

        result = ((not evaluate(w, kripke_structure, operand1, level+1)) + evaluate(w, kripke_structure, operand2, level+1)) > 0

        print "%s-%s" % ("|\t" * (level), str(result))
        #print "%s%s   I(=>)   \t%s   =   %s" % ("|\t" * (level), operand1, operand2, str(result))

        return result
    elif op == "<=>":
        brackets = 0
        for i in range(len(expression)):
            if expression[i] == "," and brackets == 0:
                break
            if expression[i] == "(":
                brackets += 1
            elif expression[i] == ")":
                brackets -= 1

        operand1 = expression[0:i].lstrip(" ").rstrip(" \n")
        operand2 = expression[i+1:].lstrip(" ").rstrip(" \n")

        result = evaluate(w, kripke_structure, operand1, level+1) == evaluate(w, kripke_structure, operand2, level+1)

        print "%s-%s" % ("|\t" * (level), str(result))
        # print "%s%s   E(<=>)   \t%s   =   %s" % ("|\t" * (level), operand1, operand2, str(result))

        return result
    elif op == "~":
        result = not evaluate(w, kripke_structure, expression, level+1)

        print "%s-%s" % ("|\t" * (level), str(result))
        #print "%s~(not)   \t%s   =   %s" % ("|\t" * (level), expression, str(result))

        return result
    elif op == "EX":
        result = ex(w, kripke_structure, expression, level)

        print "%s-%s" % ("|\t" * (level), str(result))

        return result
    elif op == "EG":
        result = eg(w, kripke_structure, expression, level)

        print "%s-%s" % ("|\t" * (level), str(result))

        return result
    elif op == "EU":
        brackets = 0
        for i in range(len(expression)):
            if expression[i] == "," and brackets == 0:
                break
            if expression[i] == "(":
                brackets += 1
            elif expression[i] == ")":
                brackets -= 1

        operand1 = expression[0:i].lstrip(" ").rstrip(" \n")
        operand2 = expression[i+1:].lstrip(" ").rstrip(" \n")

        result = eu(w, kripke_structure, operand1, operand2, level)

        print "%s-%s" % ("|\t" * (level), str(result))

        return result
    elif op == "EF":
        result = ef(w, kripke_structure, expression, level)

        print "%s-%s" % ("|\t" * (level), str(result))

        return result
    elif op == "AX":
        result = ax(w, kripke_structure, expression, level)

        print "%s-%s" % ("|\t" * (level), str(result))

        return result
    elif op == "AG":
        result = ag(w, kripke_structure, expression, level)

        print "%s-%s" % ("|\t" * (level), str(result))

        return result
    elif op == "AG":
        result = af(w, kripke_structure, expression, level)

        print "%s-%s" % ("|\t" * (level), str(result))

        return result
    elif op == "AU":
        brackets = 0
        for i in range(len(expression)):
            if expression[i] == "," and brackets == 0:
                break
            if expression[i] == "(":
                brackets += 1
            elif expression[i] == ")":
                brackets -= 1

        operand1 = expression[0:i].lstrip(" ").rstrip(" \n")
        operand2 = expression[i+1:].lstrip(" ").rstrip(" \n")

        result = au(w, kripke_structure, operand1, operand2, level)

        print "%s-%s" % ("|\t" * (level), str(result))

        return result


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
            evaluate(formula["world"], kripke_structure, formula["formula"], 0)
        except:
            print traceback.format_exc()
            print "Invalid expression!"
        print "-------------------------------\n"
