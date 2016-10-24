import subprocess
import re

a = 1
b = 100

for fid in range(a, b + 1):
    
    # get the SATLIB benchmarks here:
    # http://www.cs.ubc.ca/~hoos/SATLIB/benchm.html 
    
    fnameSat = './satlib-benchmarks/uf50/uf50-0%s.cnf' % fid
    fnameUnsat = './satlib-benchmarks/uuf50/uuf50-0%s.cnf' % fid
    
    for (filename, expectedOutPrefix) in [(fnameSat, 'sat'), (fnameUnsat, 'unsat')]:
        
        formula = []
        current_formula = []
        lit2clauses = {}
    
        with open(filename, 'r') as file:
            for line in (l.strip() for l in file.readlines()):
                if not line.startswith('c'):
                    parts = re.split(r'\s+', line)
                    if parts[0] == 'p':
                        n_vars, n_clauses = map(int, parts[2:4])
                    elif len(parts) > 1 and n_clauses > 0:
                        formula.append(set([int(slit) for slit in parts[:-1]]))
                        current_formula.append(set([int(slit) for slit in parts[:-1]]))
                        n_clauses -= 1
        
        output = subprocess.check_output(['./ggsat', filename])
        
        if not output.startswith(expectedOutPrefix):
            
            print 'WRONG!!!'
            exit(0)
        
        elif expectedOutPrefix == 'sat':
            
            sat_asn = output[4:-1]
            sat_asn = sat_asn.split()
            sat_asn = [False if v[0] == '-' else True for v in sat_asn]
            
            fsat = True
            
            for clause in formula:
                csat = False
                
                for lit in clause:
                    if sat_asn[abs(lit) - 1] == (True if lit > 0 else False):
                        csat = True
                        break
                
                if not csat:
                    print 'clause %s not true' % clause
                    fsat = False
                    break
            
            if fsat:
                #print 'Correct! (%s)' % filename
                pass
            else:
                print 'WRONG!!!'
                exit(0)
        
        else:
            #print 'Correct! (%s)' % filename  
            pass
            