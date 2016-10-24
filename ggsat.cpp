#include <algorithm>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <deque>
#include <set>
#include <map>
#include <ctime>
#include <thread>
#include <mutex>
#include <atomic>
#include <chrono>
#include <memory>
#include <cctype>
#include <cstdlib>


struct Clause {
    std::vector<int> literals;    
    
    int sat_lit_count = 0;
    int unsat_lit_count = 0;    
};


struct ThreadData {
    std::vector<Clause> current_formula;
    std::string current_assignment;
    
    int assigned_var_count = 0;

    std::string task;
    bool working = false;
};


int n_threads = 1;

std::atomic<int> working_threads;
std::atomic<bool> done;
std::atomic<bool> sat(false);

std::deque<std::string> tasks;
std::mutex mtx_tasks;

std::vector<ThreadData> t_data;
std::mutex g_mtx;

std::vector<Clause> formula;
std::map<int, std::vector<int>> lit2clauses;

int n_vars, n_clauses;

std::map<int, double> varActivity;
std::map<int, double> clauseActivity;


void updateVarActivity() {
    
    if (clauseActivity.empty()) {
        for (int i = 0; i < n_clauses; ++ i) {
            clauseActivity[i] = 1.0;
        }
    }
    
    varActivity.clear();
    
    double total = 0.0;
    
    for (int cid = 0; cid < n_clauses; ++ cid) {
        
        double ca = clauseActivity[cid];
        
        for (int lit : formula[cid].literals) {
            varActivity[lit > 0 ? lit : -lit] += ca;
            total += ca;    
        }
    }
    
    for (int var = 1; var <= n_vars; ++ var) {
        varActivity[var] /= total;    
    }       
}


void updateClauseActivity() {

    if (varActivity.empty()) {
        for (int i = 1; i <= n_vars; ++ i) {
            varActivity[i] = 1.0;
        }
    }
    
    clauseActivity.clear();
    
    double total = 0.0;
    
    for (int var = 1; var <= n_vars; ++ var) {
        
        double va = varActivity[var];
        
        for (int cid : lit2clauses[var]) {
            clauseActivity[cid] += va;
            total += va;
        }
        
        for (int cid : lit2clauses[-var]) {
            clauseActivity[cid] += va;
            total += va;
        }
    }
    
    for (int cid = 0; cid < n_clauses; ++ cid) {
        clauseActivity[cid] /= total;    
    }
}


void print_sat_assignment(const std::string & sat_asn) {
    for (int i = 0; i < n_vars; ++ i) {
        std::cout << ' ' << (sat_asn[i] == '0' ? -i-1 : i+1);
    }
}


void set_variable(int t_id, int lit) {
    t_data[t_id].current_assignment[(lit > 0 ? lit : -lit) - 1] = lit < 0 ? '0' : '1';
    ++t_data[t_id].assigned_var_count;
    
    {
        auto & clause_list = lit2clauses[-lit];
        for (auto & clause : clause_list) {
            ++ t_data[t_id].current_formula[clause].unsat_lit_count;
        }
    }
    
    {
        auto & clause_list = lit2clauses[lit];
        for (auto & clause : clause_list) {
            ++ t_data[t_id].current_formula[clause].sat_lit_count;
        }
    }
}


void clear_variable(int t_id, int lit) {
    t_data[t_id].current_assignment[(lit > 0 ? lit : -lit) - 1] = '*';
    --t_data[t_id].assigned_var_count;
    
    {
        auto & clause_list = lit2clauses[-lit];
        for (auto & clause : clause_list) {
            -- t_data[t_id].current_formula[clause].unsat_lit_count;
        }
    }
    
    {
        auto & clause_list = lit2clauses[lit];
        for (auto & clause : clause_list) {
            -- t_data[t_id].current_formula[clause].sat_lit_count;
        }
    }
}


bool contradiction(int t_id) {

    std::set<int> implied_lits;

    auto & current_formula = t_data[t_id].current_formula;
    auto & current_assignment = t_data[t_id].current_assignment;

    for (int i = 0; i < current_formula.size(); ++i) {
        auto & clause = current_formula[i];
        int size = clause.literals.size();
        if (clause.unsat_lit_count == size) {
            return true;
        }
        if (clause.unsat_lit_count == size - 1 && clause.sat_lit_count == 0) {
            for (auto lit : clause.literals) {
                
                char c = current_assignment[lit > 0 ? lit - 1 : -lit - 1];
                
                if (c == '*') {
                    implied_lits.insert(lit);
                    break;                    
                }
            }
        }
    }

    if (!implied_lits.empty()) {
        for (auto & lit : implied_lits) {
            set_variable(t_id, lit);
        }
        bool ret = contradiction(t_id);
        for (auto & lit : implied_lits) {
            clear_variable(t_id, lit);
        }
        return ret;
    }

    if (t_data[t_id].assigned_var_count == n_vars) {
        std::lock_guard<std::mutex> lock(g_mtx);
        if (!sat) {
            sat = true;
            std::cout << "sat";
            print_sat_assignment(t_data[t_id].current_assignment);
            std::cout << std::endl;
        }
    }

    return false;
}


void dpll(int t_id, int level = 0) {

    if (sat) { return; }

    if (contradiction(t_id)) { return; }

    if (t_data[t_id].assigned_var_count < n_vars) {
        auto & current_assignment = t_data[t_id].current_assignment;
        
        int varPos = -1;
        
        
        for (int i = 0; i < n_clauses; ++i) {
        
            auto & clause = t_data[t_id].current_formula[i];
            
            int size = clause.literals.size();
            
            if (clause.sat_lit_count == 0 && clause.unsat_lit_count != size) {
                for (auto lit : clause.literals) {
                    varPos = lit > 0 ? lit - 1 : -lit - 1;
                    char c = current_assignment[varPos];
                    
                    if (c == '*') {
                            goto var_chosen;
                    }
                }
            }
        }    
        
        var_chosen:
        
        auto split = false;

        if (working_threads < n_threads) {
            std::lock_guard<std::mutex> lock(mtx_tasks);

            if (working_threads < n_threads && tasks.empty()) {
                std::string task = current_assignment;
                task[varPos] = '1';
                tasks.push_back(task);
                split = true;
            }
        }

        for (int j = 0; j < (split ? 1 : 2); ++j) {
            int lit = (varPos + 1) * (j == 0 ? -1 : 1);
            set_variable(t_id, lit);
            dpll(t_id, level + 1);
            clear_variable(t_id, lit);
        }
        
    }
    else {
        std::lock_guard<std::mutex> lock(g_mtx);
        if (!sat) {
            sat = true;
            std::cout << "sat";
            print_sat_assignment(t_data[t_id].current_assignment);
            std::cout << std::endl;
        }
    }
}


void strip(std::string & str) {
    
    while (std::isspace(str[0])) {
        str = str.substr(1);
    }
    
    int len = str.size();
    
    while (std::isspace(str[len - 1])) {
        str = str.substr(0, len - 1);
        -- len;
    }
}


void split_on_ws(std::string str, std::vector<std::string> & ret) {
    
    std::string part;
    std::istringstream strin(str);
    
    ret.clear();
    
    while (strin >> part) {
        ret.push_back(part);
    }
}


void error_quit(std::string msg) {
    std::cout << "error - " << msg << std::endl;    
    std::exit(0);
}


int main(int argc, char ** argv) {
    
    if (argc != 2) {
        error_quit("usage: ggsat <filename>");
    }

    int n_cores = std::thread::hardware_concurrency();

    if (n_cores < 2) {
        n_threads = 1;
    }
    else if (n_cores < 4) {
        n_threads = 2;
    }
    else if (n_cores < 8) {
        n_threads = 4;
    }
    else {
        n_threads = 8;
    }
    

    t_data.resize(n_threads);

    std::ifstream fin(argv[1]);

    if (!fin) {
        error_quit("could not open input file");
    }

    std::string line;
    std::string token;
    int number;
    
    int n_clauses_read = 0;
    
    std::vector<std::string> line_parts;
    
    bool parse_preamble = true;
    
    Clause cur_clause;
    
    while (std::getline(fin, line)) {
        
        if (parse_preamble) {
        
            strip(line);
        
            if (line == "") continue;
            
            int line_len = line.size();
            
            if (line_len == 1 && line[0] == 'c') continue;
            
            if (line_len >= 2) {

                if (line[0] == 'c' && std::isspace(line[1])) continue;
                
                if (line[0] == 'p' && std::isspace(line[1])) {
                    
                    std::istringstream lin(line);
                    
                    lin >> token >> token >> n_vars >> n_clauses;
                    
                    if (token != "cnf") error_quit("bad preamble format");
                    
                    if (!lin) error_quit("bad preamble format");
                    
                    if (!lin.eof()) error_quit("bad preamble format");
                    
                    if (n_vars <= 0) error_quit("number of variables must be positive");
                    
                    if (n_clauses <= 0) error_quit("number of clauses must be positive");
                    
                    parse_preamble = false;
                    
                    formula.resize(n_clauses);
                    
                    for (int i = 0; i < n_threads; ++i) {
                        t_data[i].current_formula.resize(n_clauses);
                    }
                    
                } else {
                    error_quit("bad preamble format");                
                }
                
            }  
            
        } else { // parse clauses
            
            split_on_ws(line, line_parts);
            
            // this is needed so that the parser can handle SATLIB benchmark files
            if (line_parts[0] == "%") break; 
            
            for (int i = 0; i < line_parts.size(); ++ i) {
                
                if (line_parts[i] == "0") {
                    
                    if (n_clauses_read < n_clauses) {
                        formula[n_clauses_read ++] = cur_clause;
                        cur_clause.literals.clear();
                    } else {
                        error_quit("clause number inconsistency");
                    }              
                    
                } else {
                    
                    std::istringstream pin(line_parts[i]);
                    
                    int lit;
                    
                    pin >> lit;
                    
                    if (pin && pin.eof()) {
                        
                        if (lit * lit > n_vars * n_vars) {
                            error_quit("variable number inconsistency");
                        }
                        
                        cur_clause.literals.push_back(lit);
                        
                        
                    } else {
                        error_quit("bad literal format");
                    }                       
                }   
            }   
        }
    }
    
    if (!cur_clause.literals.empty()) {
        if (n_clauses_read == n_clauses - 1) {
            formula[n_clauses_read ++] = cur_clause;
            cur_clause.literals.clear();
        } else {
            error_quit("clause number inconsistency");
        }        
    }
    
    if (n_clauses_read != n_clauses) {
        error_quit("clause number inconsistency");
    }   
    
    if (n_clauses_read == 0) {
        error_quit("bad input file format (empty file?)");
    }
    
    for (int i = 0; i < n_threads; ++i) {
        t_data[i].current_assignment = std::string(n_vars, '*');
        t_data[i].assigned_var_count = 0;
    }

    for (int i = 0; i < formula.size(); ++i) {
        auto & clause = formula[i];
        for (auto & lit : clause.literals) {
            lit2clauses[lit].push_back(i);
        }
    }
    
    for (int i = 0; i < 10; ++ i) {
        updateVarActivity();
        updateClauseActivity();
    }
    
    std::vector<int> varIds;
    std::vector<int> clauseIds;
    
    for (int var = 1; var <= n_vars; ++ var) {
        varIds.push_back(var);
    }
    
    for (int cid = 0; cid < n_clauses; ++ cid) {
        clauseIds.push_back(cid);
    }
    
    std::sort(varIds.begin(), varIds.end(), 
        [&](int vid1, int vid2) {
            return varActivity[vid1] > varActivity[vid2];
        });
        
    std::sort(clauseIds.begin(), clauseIds.end(), 
        [&](int cid1, int cid2) {
            return clauseActivity[cid1] > clauseActivity[cid2];
        });
        
    std::vector<Clause> oldFormula(formula);
    
    for (int cid = 0; cid < n_clauses; ++ cid) {
        formula[cid] = oldFormula[clauseIds[cid]];
        
        std::sort(formula[cid].literals.begin(), formula[cid].literals.end(),
            [&](int l1, int l2) {
                return varActivity[l1 > 0 ? l1 : -l1] > varActivity[l2 > 0 ? l2 : -l2];    
            });
    }
    
    lit2clauses.clear();
    
    for (int i = 0; i < formula.size(); ++i) {
        auto & clause = formula[i];
        for (auto & lit : clause.literals) {
            lit2clauses[lit].push_back(i);
        }
    }

    std::vector<std::shared_ptr<std::thread>> threads;
    
    tasks.push_back(std::string(n_vars, '*'));

    working_threads = 0;
    done = false;

    auto sleep_duration_short = std::chrono::milliseconds(1);
    
    for (int i = 0; i < n_threads; ++i) {
        
        threads.push_back(std::make_shared<std::thread>([i, sleep_duration_short] {

            while (true) {

                if (!t_data[i].working) {

                    if (!tasks.empty()) {
                        std::lock_guard<std::mutex> lock(mtx_tasks);
                        if (!tasks.empty()) {

                            t_data[i].working = true;
                            ++working_threads;
                            auto task = tasks.front();
                            tasks.pop_front();
                            t_data[i].task = task;

                            for (int j = 0; j < formula.size(); ++j) {
                                t_data[i].current_formula[j] = formula[j];
                            }

                            t_data[i].current_assignment = std::string(n_vars, '*');
                            t_data[i].assigned_var_count = 0;

                            for (int j = 0; j < n_vars; ++j) {
                                char c = task[j];
                                if (c == '1') {
                                    set_variable(i, j + 1);
                                }
                                else if (c == '0') {
                                    set_variable(i, -j - 1);
                                }
                            }

                        }
                    }

                    if (t_data[i].working) {
                        dpll(i);
                        t_data[i].working = false;
                        --working_threads;
                    }

                }

                if (working_threads == 0) {
                    std::lock_guard<std::mutex> lock(mtx_tasks);
                    if (working_threads == 0 && tasks.empty()) {
                        done = true;
                    }
                }

                if (done) {
                    return;
                }

                std::this_thread::sleep_for(sleep_duration_short);
            }

        }));
    }
    
    auto sleep_duration_long = std::chrono::milliseconds(10);

    while (!done) {
        std::this_thread::sleep_for(sleep_duration_long);
    }

    for (int i = 0; i < n_threads; ++i) {
        threads[i]->join();
    }

    if (!sat) {
        std::cout << "unsat" << std::endl;
    }
}
