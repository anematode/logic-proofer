import re

def AND(A,B):
    return (A and B)

def OR(A,B):
    return (A or B)

def NOT(A):
    return (not A)

def IMPLY(A,B):
    return not (A and not B)

def BIDIR(A,B):
    return (A == B)

def ASSERT(A):
    return A

def process_premises(premises):
    for premise in premises:
        for alias in ["^"]:
            premise = premise.replace(alias," and ")
        for alias in ["\\/","v"]:
            premise = premise.replace(alias," or ")
        for alias in ["->", "-->", "imply", "implies"]:
            premise = premise.replace(alias," imp ")
        for alias in ["<->", "<-->", "iff"]:
            premise = premise.replace(alias," bid ")
        for alias in ["~", "-"]:
            premise = premise.replace(alias," not ")
        premise = ' '.join(premise.split())
        yield premise

def functionalize_statement(statement):
    i = len(statement) - 1
    while (i > -1):
        if (statement[i:i+3] == "not"):
            start = i+3
            end = len(statement)
            for j in xrange(i+4,len(statement)):
                if (statement[j] == ' '):
                    end = j
                    break
            statement = statement[:i] + "NOT[" + statement[start:end].replace(' ','') + "]" + statement[end:]
        i -= 1
    i = len(statement) - 1
    while (i > -1):
        if (statement[i:i+3] == "and"):
            conseqstart = i+3
            conseqend = len(statement)
            for j in xrange(i+4,len(statement)):
                if (statement[j] == ' '):
                    conseqend = j
                    break
            antestart = 0
            anteend = i
            for j in xrange(i-2,-1,-1):
                if (statement[j] == ' '):
                    antestart = j
                    break
            statement = statement[:antestart] + "AND[" + statement[antestart:anteend].replace(' ','') + "," + \
            statement[conseqstart:conseqend].replace(' ','') + "]" + statement[conseqend:]
            i = antestart
        i -= 1
    i = len(statement) - 1
    while (i > -1):
        if (statement[i:i+2] == "or"):
            conseqstart = i+2
            conseqend = len(statement)
            for j in xrange(i+3,len(statement)):
                if (statement[j] == ' '):
                    conseqend = j
                    break
            antestart = 0
            anteend = i
            for j in xrange(i-2,-1,-1):
                if (statement[j] == ' '):
                    antestart = j
                    break
            statement = statement[:antestart] + "OR[" + statement[antestart:anteend].replace(' ','') + "," + \
            statement[conseqstart:conseqend].replace(' ','') + "]" + statement[conseqend:]
            i = antestart
        i -= 1
    i = len(statement) - 1
    while (i > -1):
        if (statement[i:i+3] == "imp"):
            conseqstart = i+3
            conseqend = len(statement)
            for j in xrange(i+4,len(statement)):
                if (statement[j] == ' '):
                    conseqend = j
                    break
            antestart = 0
            anteend = i
            for j in xrange(i-2,-1,-1):
                if (statement[j] == ' '):
                    antestart = j
                    break
            statement = statement[:antestart] + "IMPLY[" + statement[antestart:anteend].replace(' ','') + "," + \
            statement[conseqstart:conseqend].replace(' ','') + "]" + statement[conseqend:]
            i = antestart
        i -= 1
    i = len(statement) - 1
    while (i > -1):
        if (statement[i:i+3] == "bid"):
            conseqstart = i+3
            conseqend = len(statement)
            for j in xrange(i+4,len(statement)):
                if (statement[j] == ' '):
                    conseqend = j
                    break
            antestart = 0
            anteend = i
            for j in xrange(i-2,-1,-1):
                if (statement[j] == ' '):
                    antestart = j
                    break
            statement = statement[:antestart] + "BIDIR[" + statement[antestart:anteend].replace(' ','') + "," + \
            statement[conseqstart:conseqend].replace(' ','') + "]" + statement[conseqend:]
            i = antestart
        i -= 1
    return statement

def evaluate_statement(statement,args):
    spl_statement = list(statement)
    for i in xrange(len(statement)):
        if (spl_statement[i] in ['(',','] and spl_statement[i+1].istitle() and not spl_statement[i+2].istitle()):
            spl_statement[i+1] = str(args[spl_statement[i+1]])
    print ''.join(spl_statement)
    return eval(''.join(spl_statement))

def functionalize_statements(premises):
    for premise in ['(' + p + ')' for p in premises]:
        while True:
            max_depth = 0
            depth = 0
            for i in xrange(len(premise)):
                if (premise[i] == '('):
                    depth += 1
                    if (depth > max_depth):
                        max_depth = depth
                elif (premise[i] == ')'):
                    depth -= 1
            depth = 0
            start = 0
            clen = len(premise)
            for i in xrange(clen):
                if (i >= clen):
                    break
                if (premise[i] == '('):
                    depth += 1
                    start = i
                elif (premise[i] == ')'):
                    depth -= 1
                    if (depth == max_depth - 1):
                        premise = premise[:start] + functionalize_statement(premise[start+1:i]) + premise[i+1:]
                        clen = len(premise)
            if (max_depth == 0):
                break
        yield ('ASSERT[' + premise + ']').replace('[','(').replace(']',')')

def event_names(premises):
    events = []
    for premise in premises:
        for i in xrange(len(premise)):
            if (premise[i] in ['(',','] and premise[i+1].istitle() and not premise[i+2].istitle()):
                event = premise[i+1]
                if (event not in events):
                    events.append(event)
    return events

def childify(premise):
    ptypeend = 0
    for i in xrange(len(premise)):
        if (not premise[i].istitle()):
            ptypeend = i
            break
    ptype = premise[:ptypeend]
    pcontent = premise[ptypeend+1:-1]
    if ('(' not in pcontent and ',' not in pcontent):
        return [ptype,pcontent]
    if (ptype in ['ASSERT','NOT']):
        return [ptype,childify(pcontent)]
    depth = 0
    splindex = 0
    for i in xrange(len(pcontent)):
        if (pcontent[i] == '('):
            depth += 1
        elif (pcontent[i] == ')'):
            depth -= 1
        if (depth == 0):
            if (pcontent[i] == ','):
                splindex = i
                break
    first = pcontent[:i]
    second = pcontent[i+1:]

    if ('(' in first):
        first = childify(first)
    if ('(' in second):
        second = childify(second)
    
    return [ptype,first,second]

def unchildify_todisplay(child):
    if (isinstance(child,basestring)):
        return child
    if (child[0] == 'ASSERT'):
        return unchildify_todisplay(child[1])
    if (child[0] == 'BIDIR'):
        return '(' + unchildify_todisplay(child[1]) + ' <-> ' + unchildify_todisplay(child[2]) + ')'
    if (child[0] == 'IMPLY'):
        return '(' + unchildify_todisplay(child[1]) + ' -> ' + unchildify_todisplay(child[2]) + ')'
    if (child[0] == 'AND'):
        return '(' + unchildify_todisplay(child[1]) + ' ^ ' + unchildify_todisplay(child[2]) + ')'
    if (child[0] == 'OR'):
        return '(' + unchildify_todisplay(child[1]) + ' v ' + unchildify_todisplay(child[2]) + ')'
    if (child[0] == 'NOT'):
        return '~' + unchildify_todisplay(child[1])

def unchildify(child):
    if (isinstance(child,basestring)):
        return child
    if (child[0] == 'ASSERT'):
        return unchildify(child[1])
    if (child[0] == 'BIDIR'):
        return 'BIDIR(%s,%s)' % (unchildify(child[1]),unchildify(child[2]))
    if (child[0] == 'IMPLY'):
        return 'IMPLY(%s,%s)' % (unchildify(child[1]),unchildify(child[2]))
    if (child[0] == 'AND'):
        return 'AND(%s,%s)' % (unchildify(child[1]),unchildify(child[2]))
    if (child[0] == 'OR'):
        return 'OR(%s,%s)' % (unchildify(child[1]),unchildify(child[2]))
    if (child[0] == 'NOT'):
        return 'NOT(%s)' % unchildify(child[1])

def add_child(child):
    global childs,pertinents
    for pchild in childs:
        if (child == pchild):
            return
    childs.append(child)
    negated_child = ["NOT",child]
    pertinents = [y for y in pertinents if (y != child and y != negated_child)]

def attempt_add_statement():
    global childs
    for i1 in xrange(len(childs)):
        s1 = childs[i1]
        if (s1[0] == 'ASSERT' and s1[1][0] == 'NOT' and s1[1][1][0] == 'AND'):
            if (add_child(['ASSERT',['OR',['NOT',s1[1][1][1]],['NOT',s1[1][1][2]]]])): continue
            reasons.append("DL %s" % (i1+1))
        if (s1[0] == 'ASSERT' and s1[1][0] == 'NOT' and s1[1][1][0] == 'OR'):
            if (add_child(['ASSERT',['AND',['NOT',s1[1][1][1]],['NOT',s1[1][1][2]]]])): continue
            reasons.append("DL %s" % (i1+1))
            
    for i1 in xrange(len(childs)):
        for i2 in xrange(len(childs)):
            if (i1 != i2):
                s1 = childs[i1]
                s2 = childs[i2]
                if (s1[0] == 'ASSERT' and s2[0] == 'ASSERT'):
                    if (s2[1][0] == 'IMPLY'):
                        if (s1[1] == s2[1][1]):
                            # Ponendo Ponens
                            if (add_child(['ASSERT',s2[1][2]])): continue
                            reasons.append("PP %s,%s" % (min(i1+1,i2+2),max(i1+1,i2+1)))
                    if (s1[1][0] == 'IMPLY' and s2[1][0] == 'IMPLY'):
                        if (s1[1][2] == s2[1][1]):
                            # Hypothetical Syllogism
                            if (add_child(['ASSERT',['IMPLY',s1[1][1],s2[1][2]]])): continue
                            reasons.append("HS %s,%s" % (min(i1+1,i2+1),max(i1+1,i2+1)))
                    if (s1[1][0] == 'OR' and s2[1][0] == 'NOT'):
                        if (s1[1][1] == s2[1][1]):
                            # Tolendo Ponens, (P v Q) ^ ~P -> Q
                            if (add_child(['ASSERT',s1[1][2]])): continue
                            reasons.append("TP %s,%s" % (min(i1+1,i2+1),max(i1+1,i2+1)))
                        if (s1[1][2] == s2[1][1]):
                            # Tolendo Ponens, (Q v P) ^ ~P -> Q
                            if (add_child(['ASSERT',s1[1][1]])): continue
                            reasons.append("TP %s,%s" % (min(i1+1,i2+1),max(i1+1,i2+1)))
                    if (s1[1][0] == 'IMPLY' and s2[1][0] == 'NOT'):
                        if (s1[1][2] == s2[1][1]):
                            # Tolendo Tolens, (P -> Q) ^ ~Q -> ~P
                            if (add_child(['ASSERT',['NOT',s1[1][1]]])): continue
                            reasons.append("TT %s,%s" % (min(i1+1,i2+1),max(i1+1,i2+1)))
                    if (s1[1][0] == 'IMPLY' and s2[1][0] == 'IMPLY'):
                        if (s1[1][1] == s2[1][2] and s1[1][2] == s2[1][1]):
                            # Biconditional Introduction, (P -> Q) ^ (Q <- P)
                            if (add_child(['ASSERT',['BIDIR',s1[1][1],s1[1][2]]])): continue
                            reasons.append("BD %s,%s" % (min(i1+1,i2+1),max(i1+1,i2+1)))


def logically_equivalent(child1,child2):
    child1 = unchildify(child1)
    child2 = unchildify(child2)
    evts = event_names([child1,child2])
    for i in xrange(2**len(evts)):
        dct = {}
        binr = list("{0:b}".format(i).zfill(len(evts)))
        for j,evt in enumerate(evts):
            dct[evt] = binr[j]
        if (evaluate_statement(child1,dct) != evaluate_statement(child2,dct)):
            return False
    return True

def add_pertinent(child):
    global pertinents
    if (child not in pertinents):
        pertinents.append(child)

def add_pertinents(child):
    if (child[0] == 'ASSERT'):
        try:
            add_pertinent(child[1][1])
            add_pertinent(child[1][2])
        except:
            pass
        
                            
print "Welcome to the Automatic Proof Solver!"

premises = []

print "Please type in your premises.\nType in \"done\" once you are done with your premises and would like to continue.\nType in \"help\" if you are confused."
while (True):
    premise = raw_input('> ')
    
    if (premise.replace(' ','').lower() == "help"):
        print "The symbols are as follows:\n"
        print "And, Conjunction: \"and\", \"^\""
        print "Or, Disjunction: \"or\", \"\\/\", \"v\""
        print "Imply: \"->\", \"-->\", \"imply\", \"implies\""
        print "Logical Biconditional: \"<->\", \"<-->\", \"iff\""
        print "Not: \"~\", \"-\", \"not\"\n"
        print "For example, the logical statement (A ^ B) v C -> ~D can be written in any of the following ways:\n"
        print "(A ^ B) v C -> ~D"
        print "(A and B) or C implies not D"
        print "(A^B)\\/C->-D\n"
        print "Events are always capital letters.\n"
        print "Please type in your premises.\nType in \"done\" once you are done with your premises and would like to continue.\nType in \"help\" if you are confused."
        continue

    if (premise.replace(' ','').lower() == "done"):
        break

    premises.append(premise)

print "What would you like to prove?"
desire = childify(list(functionalize_statements(list(process_premises([raw_input('>')]))))[0])

print desire

premises = list(functionalize_statements(list(process_premises(premises))))
events = event_names(premises)

print premises
print events

pertinents = []

childs = [childify(premise) for premise in premises]
reasons = ["P"] * len(childs)
prevlen = len(childs)

for child in childs:
    add_pertinents(child)

print pertinents

while True:
    attempt_add_statement()
    newlen = len(childs)
    if (desire in childs[prevlen-1:]):
        break
    if (newlen == prevlen):
        break
    prevlen = newlen

for i in xrange(len(childs)):
    print unchildify_todisplay(childs[i]) + '\t' + reasons[i]

print childs
#print logically_equivalent(childs[0],childs[1])
