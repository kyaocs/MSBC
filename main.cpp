//
//  main.cpp
//  MSBC
//
//  Created by kai on 23/03/2021.
//

#include "Timer.h"
#include "Utility.h"
#include "LinearHeap.h"

ui n; //number of vertices
ui m; //number of edges
ui pm; //number of positive edges
ui nm; //number of negative edges
ui d_MAX; //max degree
ui max_core; //degeneracy number
int tau; //threshold
int Mtau; //polarization factor
pair<vector<ui>, vector<ui>> cur_MC; //the largest MSBC found so far
int UB; //UB of MSBC


ui CntEgoNet;
ui num_of_ori_edges;
ui num_of_now_edges;
ui num_of_after_reduction_now_edges;

ui * p_pstart;
ui * p_pend;
ui * p_edges;

ui * n_pstart;
ui * n_pend;
ui * n_edges;

ui * p_pstart_o;
ui * p_pend_o;
ui * p_edges_o;

ui * n_pstart_o;
ui * n_pend_o;
ui * n_edges_o;

ui * degree;
ui * p_degree;
ui * n_degree;

ui * core;
ui * peel_s;
ui * bit_del;
ui * PNdeg;
ui max_PorNdeg;

int ** Matrix;
ui * trans;
//ui * trs;
ui * inPN;
ui * vs_core;
ui * vs_color;

//case study
ui * ori_id;
unordered_map<ui, string> id2str;

dense_hash_map<ui, ui> * sup_pp;
dense_hash_map<ui, ui> * sup_nn;
dense_hash_map<ui, ui> * sup_np;
dense_hash_map<ui, int> * e_sign;
dense_hash_map<ui, bool> * e_del;

vector<ui> maxC;

void init_hash()
{
    sup_pp = new dense_hash_map<ui, ui>[n];
    sup_nn = new dense_hash_map<ui, ui>[n];
    sup_np = new dense_hash_map<ui, ui>[n];
    e_sign = new dense_hash_map<ui, int>[n];
    e_del = new dense_hash_map<ui, bool>[n];
    
    
    for(ui i = 0; i < n; i++){
        sup_pp[i].resize(degree[i]);
        sup_nn[i].resize(degree[i]);
        sup_np[i].resize(degree[i]);
        e_sign[i].resize(degree[i]);
        e_del[i].resize(degree[i]);
    }
    for(ui i = 0; i < n; i++){
        sup_pp[i].set_empty_key(INF);
        sup_nn[i].set_empty_key(INF);
        sup_np[i].set_empty_key(INF);
        e_sign[i].set_empty_key(INF);
        e_del[i].set_empty_key(INF);
    }
    for(ui i = 0; i < n; i++){
        for(ui j = p_pstart[i]; j < p_pstart[i+1]; j++){
            sup_pp[i][p_edges[j]] = 0; sup_pp[p_edges[j]][i] = 0;
            sup_nn[i][p_edges[j]] = 0; sup_nn[p_edges[j]][i] = 0;
            sup_np[i][p_edges[j]] = 0; sup_np[p_edges[j]][i] = 0;
            e_sign[i][p_edges[j]] = 1; e_sign[p_edges[j]][i] = 1;
            e_del[i][p_edges[j]] = 0; e_del[p_edges[j]][i] = 0;
        }
        for(ui j = n_pstart[i]; j < n_pstart[i+1]; j++){
            sup_pp[i][n_edges[j]] = 0; sup_pp[n_edges[j]][i] = 0;
            sup_nn[i][n_edges[j]] = 0; sup_nn[n_edges[j]][i] = 0;
            sup_np[i][n_edges[j]] = 0; sup_np[n_edges[j]][i] = 0;
            e_sign[i][n_edges[j]] = -1; e_sign[n_edges[j]][i] = -1;
            e_del[i][n_edges[j]] = 0; e_del[n_edges[j]][i] = 0;
        }
    }
}

void load_graph(string input_graph)
{
    string buffer;
    ifstream input_file(input_graph, ios::in);
    
    if (!input_file.is_open()){
        cout << "cannot open file : "<<input_graph<<endl;exit(1);
    }
    else{
        input_file >> n >> m;
        map<ui, int> * s_G = new map<ui, int>[n];
        ui tu, tv;
        int flag;
        while (input_file >> tu >> tv >> flag){
            if(tu == tv) continue;
            assert(tu >= 0 && tu < n);
            assert(tv >= 0 && tv < n);
            assert(flag == 1 || flag == -1);
            s_G[tu].insert(make_pair(tv, flag));
            s_G[tv].insert(make_pair(tu, flag));
        }
        m = 0; pm = 0; nm = 0;
        for(ui i = 0; i < n; i++){
            const map<ui, int> & nei = s_G[i];
            for(auto e : nei){
                if(e.second == 1)
                    ++ pm;
                else
                    ++ nm;
            }
            m += nei.size();
        }
        assert(m%2 == 0);assert(pm%2 == 0);assert(nm%2 == 0);
        m /= 2; pm /= 2; nm /= 2;

        input_file.close();
        
        p_pstart = new ui[n+1];
        p_edges = new ui[2*pm];
        p_pend = new ui[n];
        n_pstart = new ui[n+1];
        n_edges = new ui[2*nm];
        n_pend = new ui[n];
        
        degree = new ui[n];
        p_degree = new ui[n];
        n_degree = new ui[n];
        
        //construct positive edges
        p_pstart[0] = 0;
        for(ui i = 0; i < n; i++){
            const map<ui, int> & nei = s_G[i];
            ui start_idx = p_pstart[i];
            int t_d = 0;
            for(auto e : nei){
                if(e.second == 1){
                    p_edges[start_idx ++] = e.first;
                    ++ t_d;
                }
            }
            p_pstart[i+1] = start_idx;
            p_degree[i] = t_d;
        }
        assert(p_pstart[n] == 2*pm);
        
        //construct negative edges
        n_pstart[0] = 0;
        for(ui i = 0; i < n; i++){
            const map<ui, int> & nei = s_G[i];
            ui start_idx = n_pstart[i];
            int t_d = 0;
            for(auto e : nei){
                if(e.second == -1){
                    n_edges[start_idx ++] = e.first;
                    ++ t_d;
                }
            }
            n_pstart[i+1] = start_idx;
            n_degree[i] = t_d;
        }
        assert(n_pstart[n] == 2*nm);
        
        for(ui i = 0; i < n; i++){
            p_pend[i] = p_pstart[i+1];
            n_pend[i] = n_pstart[i+1];
        }
        long max_pndeg = 0;
        d_MAX = 0;
        for(ui i = 0; i < n; i++){
            degree[i] = p_degree[i] + n_degree[i];
            if(p_degree[i] * n_degree[i] > max_pndeg) max_pndeg = p_degree[i] * n_degree[i];
            if(degree[i] > d_MAX)
                d_MAX = degree[i];
        }
        delete [] s_G;
    }
//    cout<<"\t G : n = "<<n<<", pm = "<<pm<<", nm = "<<nm<<endl;
#ifdef _CaseStudy_
    input_graph.erase(input_graph.end() - 4, input_graph.end());
    input_graph.append("_map.txt"); //the mapping file should be named in this way.
    input_file.open(input_graph);
    if(!input_file.is_open()){ cout<<"cannot open map file !"<<endl; exit(1); }
    ori_id = new ui[n];
    ui vid;
    string content;
    while (input_file >> content >> vid) id2str[vid] = content;
    input_file.close();
#endif
}

bool check_SBC(pair<vector<ui>, vector<ui>> & C)
{
    vector<ui> L = C.first;
    vector<ui> R = C.second;
    bool flag = true;
    for(auto u : L){
        for(auto v : L){
            if(u == v) continue;
            ui i;
            for(i = p_pstart[u]; i < p_pend[u]; i++){
                ui w = p_edges[i];
                if(w == v) break;
            }
            if(i >= p_pend[u]){
                flag = false;
                break;
            }
        }
        if(!flag) break;
    }
    if(!flag) return flag;
    for(auto u : R){
        for(auto v : R){
            if(u == v) continue;
            ui i;
            for(i = p_pstart[u]; i < p_pend[u]; i++){
                ui w = p_edges[i];
                if(w == v) break;
            }
            if(i >= p_pend[u]){
                flag = false;
                break;
            }
        }
        if(!flag) break;
    }
    if(!flag) return flag;
    for(auto u : L){
        for(auto v : R){
            ui i;
            for(i = n_pstart[u]; i < n_pend[u]; i++){
                ui w = n_edges[i];
                if(w == v) break;
            }
            if(i >= n_pend[u]){
                flag = false;
                break;
                
            }
        }
        if(!flag) break;
    }

    return flag;
}

//greedy search until find one solution, at most 'rounds' tries.
void heu_MSBC_max_deg_inturn_find_one_stop(int rounds)
{
    if(rounds < 1) return;
    assert(psz(cur_MC) == 0);
    priority_queue<pair<ui, ui>, vector<pair<ui, ui>>, greater<pair<ui, ui>>> kset;
    for (ui i = 0; i < rounds; i++) kset.push(make_pair(miv(p_degree[i], n_degree[i]), i));
    
    for(ui i = rounds; i < n; i++){
        ui itsdeg = miv(p_degree[i], n_degree[i]);
        if(itsdeg > kset.top().first){
            kset.pop();
            kset.push(make_pair(itsdeg, i));
        }
    }
    vector<pair<ui, ui>> ordV(rounds);
    for(ui i = 0; i < rounds; i++){
        ordV[i] = kset.top();
        kset.pop();
    }
    assert(kset.empty());
    
    sort(ordV.begin(), ordV.end(), greater<>()); //increasing order
    
    ui * label = new ui[n];
    ui * vs_deg = new ui[n];
    
    for(ui round = 0; round < rounds && round < n; round++){
        ui u = ordV[round].second;
        memset(label, 0, sizeof(ui)*n);
        pair<vector<ui>, vector<ui>> res;
        res.first.push_back(u);
        vector<ui> vsP, vsN;
        for(ui i = p_pstart[u]; i < p_pend[u]; i++){
            ui v = p_edges[i];
            vsP.push_back(v);
            label[v] = 1;
        }
        for(ui i = n_pstart[u]; i < n_pend[u]; i++){
            ui v = n_edges[i];
            vsN.push_back(v);
            label[v] = 2;
        }
        for(auto e : vsP) vs_deg[e] = 0;
        for(auto e : vsN) vs_deg[e] = 0;
        for(auto e : vsP){
            for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                ui v = p_edges[i];
                if(label[v] == 1) ++ vs_deg[e];
            }
            for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                ui v = n_edges[i];
                if(label[v] == 2) ++ vs_deg[e];
            }
        }
        for(auto e : vsN){
            for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                ui v = p_edges[i];
                if(label[v] == 2) ++ vs_deg[e];
            }
            for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                ui v = n_edges[i];
                if(label[v] == 1) ++ vs_deg[e];
            }
        }
        
        while (!vsP.empty() || !vsN.empty()) {
            if(!vsP.empty() && !vsN.empty()){
                if(res.first.size() >= res.second.size()){ // next vertex will select from vsN
                    ui tmp_deg = 0;
                    ui next_v;
                    for(ui i = 0; i < vsN.size(); i++){
                        if(vs_deg[vsN[i]] >= tmp_deg){
                            tmp_deg = vs_deg[vsN[i]];
                            next_v = vsN[i];
                        }
                    }
                    res.second.push_back(next_v);
                    vector<ui> new_vsP, new_vsN;
                    assert(label[next_v] == 2);
                    for(ui i = p_pstart[next_v]; i < p_pend[next_v]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 2) new_vsN.push_back(v);
                    }
                    for(ui i = n_pstart[next_v]; i < n_pend[next_v]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 1) new_vsP.push_back(v);
                    }
                    for(auto e : vsP) label[e] = 0;
                    for(auto e : vsN) label[e] = 0;
                    vsP = new_vsP;
                    vsN = new_vsN;
                    for(auto e : vsP) label[e] = 1;
                    for(auto e : vsN) label[e] = 2;
                    for(auto e : vsP) vs_deg[e] = 0;
                    for(auto e : vsN) vs_deg[e] = 0;
                    for(auto e : vsP){
                        for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                            ui v = p_edges[i];
                            if(label[v] == 1) ++ vs_deg[e];
                        }
                        for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                            ui v = n_edges[i];
                            if(label[v] == 2) ++ vs_deg[e];
                        }
                    }
                    for(auto e : vsN){
                        for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                            ui v = p_edges[i];
                            if(label[v] == 2) ++ vs_deg[e];
                        }
                        for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                            ui v = n_edges[i];
                            if(label[v] == 1) ++ vs_deg[e];
                        }
                    }
                }
                else{ // next vertex will select from vsP
                    ui tmp_deg = 0;
                    ui next_v;
                    for(ui i = 0; i < vsP.size(); i++){
                        if(vs_deg[vsP[i]] >= tmp_deg){
                            tmp_deg = vs_deg[vsP[i]];
                            next_v = vsP[i];
                        }
                    }
                    res.first.push_back(next_v);
                    vector<ui> new_vsP, new_vsN;
                    assert(label[next_v] == 1);
                    for(ui i = p_pstart[next_v]; i < p_pend[next_v]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 1) new_vsP.push_back(v);
                    }
                    for(ui i = n_pstart[next_v]; i < n_pend[next_v]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 2) new_vsN.push_back(v);
                    }
                    for(auto e : vsP) label[e] = 0;
                    for(auto e : vsN) label[e] = 0;
                    vsP = new_vsP;
                    vsN = new_vsN;
                    for(auto e : vsP) label[e] = 1;
                    for(auto e : vsN) label[e] = 2;
                    for(auto e : vsP) vs_deg[e] = 0;
                    for(auto e : vsN) vs_deg[e] = 0;
                    for(auto e : vsP){
                        for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                            ui v = p_edges[i];
                            if(label[v] == 1) ++ vs_deg[e];
                        }
                        for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                            ui v = n_edges[i];
                            if(label[v] == 2) ++ vs_deg[e];
                        }
                    }
                    for(auto e : vsN){
                        for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                            ui v = p_edges[i];
                            if(label[v] == 2) ++ vs_deg[e];
                        }
                        for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                            ui v = n_edges[i];
                            if(label[v] == 1) ++ vs_deg[e];
                        }
                    }
                }
            }
            else if(vsP.empty() && !vsN.empty()){ // next vertex will select from vsN
                ui tmp_deg = 0;
                ui next_v;
                for(ui i = 0; i < vsN.size(); i++){
                    if(vs_deg[vsN[i]] >= tmp_deg){
                        tmp_deg = vs_deg[vsN[i]];
                        next_v = vsN[i];
                    }
                }
                res.second.push_back(next_v);
                vector<ui> new_vsP, new_vsN;
                assert(label[next_v] == 2);
                for(ui i = p_pstart[next_v]; i < p_pend[next_v]; i++){
                    ui v = p_edges[i];
                    if(label[v] == 2) new_vsN.push_back(v);
                }
                for(ui i = n_pstart[next_v]; i < n_pend[next_v]; i++){
                    ui v = n_edges[i];
                    if(label[v] == 1) new_vsP.push_back(v);
                }
                for(auto e : vsP) label[e] = 0;
                for(auto e : vsN) label[e] = 0;
                vsP = new_vsP;
                vsN = new_vsN;
                for(auto e : vsP) label[e] = 1;
                for(auto e : vsN) label[e] = 2;
                for(auto e : vsP) vs_deg[e] = 0;
                for(auto e : vsN) vs_deg[e] = 0;
                for(auto e : vsP){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                }
                for(auto e : vsN){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                }
            }
            else if (!vsP.empty() && vsN.empty()){ // next vertex will select from vsP
                ui tmp_deg = 0;
                ui next_v;
                for(ui i = 0; i < vsP.size(); i++){
                    if(vs_deg[vsP[i]] >= tmp_deg){
                        tmp_deg = vs_deg[vsP[i]];
                        next_v = vsP[i];
                    }
                }
                res.first.push_back(next_v);
                vector<ui> new_vsP, new_vsN;
                assert(label[next_v] == 1);
                for(ui i = p_pstart[next_v]; i < p_pend[next_v]; i++){
                    ui v = p_edges[i];
                    if(label[v] == 1) new_vsP.push_back(v);
                }
                for(ui i = n_pstart[next_v]; i < n_pend[next_v]; i++){
                    ui v = n_edges[i];
                    if(label[v] == 2) new_vsN.push_back(v);
                }
                for(auto e : vsP) label[e] = 0;
                for(auto e : vsN) label[e] = 0;
                vsP = new_vsP;
                vsN = new_vsN;
                for(auto e : vsP) label[e] = 1;
                for(auto e : vsN) label[e] = 2;
                for(auto e : vsP) vs_deg[e] = 0;
                for(auto e : vsN) vs_deg[e] = 0;
                for(auto e : vsP){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                }
                for(auto e : vsN){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                }
            }
            else{
                cout<<"wrong!"<<endl;
                exit(1);
            }
        }
        if(psz(res) > psz(cur_MC) && res.first.size() >= tau && res.second.size() >= tau){
            cur_MC = res;
            break;
        }
    }
}

void vertex_reduction(ui & del_count, ui * bit_del)
{
    if(tau <= 1) {cout<<"\t tau should be at least 2"<<endl; exit(1); }
    int pt = tau - 1;
    int nt = tau;
    queue<ui> Q;
    for(ui i = 0; i < n; i++) if(p_degree[i] < pt || n_degree[i] < nt) Q.push(i);
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        ++ del_count;
        bit_del[u] = 1;
        for(ui i = p_pstart[u]; i < p_pstart[u+1]; i++){
            if((p_degree[p_edges[i]]--) == pt && n_degree[p_edges[i]] >= nt){
                Q.push(p_edges[i]);
            }
        }
        for(ui i = n_pstart[u]; i < n_pstart[u+1]; i++){
            if((n_degree[n_edges[i]]--) == nt && p_degree[n_edges[i]] >= pt){
                Q.push(n_edges[i]);
            }
        }
    }
}

void shrink_on_reduced_v(ui * bit_del)
{
    ui * mapping = new ui[n];
    ui idx = 0;
    for(ui i = 0; i < n; i++) {
        if(!bit_del[i]) {
            mapping[i] = idx;
            ++ idx;
        }
    }
    
#ifdef _CaseStudy_
    idx = 0;
    for(ui i = 0; i < n; i++) if(!bit_del[i]) ori_id[idx++] = i;
#endif
    
#ifdef _DEBUG_
    cout<<"after shrink_on_reduced_v(), mapping content : "<<endl;
    for(ui i = 0; i < n; i++){
        if(!bit_del[i]){
            cout<<" "<<i<<" ---> "<<mapping[i]<<endl;
        }
    }
#endif
    
    ui * t_p_pstart = new ui[n+1];
    ui * t_p_edges = new ui[2*pm];
    ui * t_n_pstart = new ui[n+1];
    ui * t_n_edges = new ui[2*nm];
    ui new_i = 0;
    t_p_pstart[0] = 0;
    for(ui i = 0; i < n; i++) if(!bit_del[i]){
        ui pos = t_p_pstart[new_i];
        for(ui j = p_pstart[i]; j < p_pstart[i+1]; j++) if(!bit_del[p_edges[j]]){
            t_p_edges[pos++] = mapping[p_edges[j]];
        }
        t_p_pstart[++new_i] = pos;
    }
    assert(new_i == idx);
    new_i = 0;
    t_n_pstart[0] = 0;
    for(ui i = 0; i < n; i++) if(!bit_del[i]){
        ui pos = t_n_pstart[new_i];
        for(ui j = n_pstart[i]; j < n_pstart[i+1]; j++) if(!bit_del[n_edges[j]]){
            t_n_edges[pos++] = mapping[n_edges[j]];
        }
        t_n_pstart[++new_i] = pos;
    }
    assert(new_i == idx);
    n = idx;

    delete [] p_pstart;
    delete [] p_edges;
    delete [] n_pstart;
    delete [] n_edges;
    delete [] mapping;
    
    p_pstart = t_p_pstart;
    p_edges = t_p_edges;
    n_pstart = t_n_pstart;
    n_edges = t_n_edges;
    
    //update pend
    for(ui i = 0; i < n; i++){
        p_pend[i] = p_pstart[i+1];
        n_pend[i] = n_pstart[i+1];
    }
    
    d_MAX = 0;
        
    //update degree
    for(ui i = 0; i < n; i++){
        p_degree[i] = p_pstart[i+1] - p_pstart[i];
        n_degree[i] = n_pstart[i+1] - n_pstart[i];
        degree[i] = p_degree[i] + n_degree[i];
        if(degree[i] > d_MAX) d_MAX = degree[i];
    }
        
    peel_s = new ui[n];
    for(ui i = 0; i < n; i++) peel_s[i] = i;
    PNdeg = new ui[n];
    max_PorNdeg = 0;
    for(ui i = 0; i < n; i++){
        if(p_degree[i] < n_degree[i]) PNdeg[i] = p_degree[i] + 1;
        else PNdeg[i] = n_degree[i];
        if(p_degree[i] > max_PorNdeg) max_PorNdeg = p_degree[i];
        if(n_degree[i] > max_PorNdeg) max_PorNdeg = n_degree[i];
    }
}

inline void reord_deg(ui & v1, ui & v2)
{
    if(degree[v1]>degree[v2]){
        ui t = v2;
        v2 = v1;
        v1 = t;
    }
}

void edge_reduction(ui & dele_count)
{
    //counting sort by degree
    ui * vs = new ui[n];
    ui * C = new ui[d_MAX+1];
    memset(C, 0, sizeof(ui)*(d_MAX+1));
    for(ui i = 0; i < n; i++) ++ C[degree[i]];
    for(ui i = 1; i <= d_MAX; i++) C[i] += C[i-1];
    for(ui i = 0; i < n; i++) vs[--C[degree[i]]] = i;
    
    //count triangle
    ui * mark = new ui[n];
    memset(mark, 0, sizeof(ui)*n);
    ui * del = new ui[n];
    memset(del, 0, sizeof(ui)*n);

    init_hash();

    for(int i = n-1; i >= 0; i--){
        ui u = vs[i];
        for(ui j = p_pstart[u]; j < p_pstart[u+1]; j++) mark[p_edges[j]] = 1;
        for(ui j = n_pstart[u]; j < n_pstart[u+1]; j++) mark[n_edges[j]] = 2;
        for(ui j = p_pstart[u]; j < p_pstart[u+1]; j++){
            ui v = p_edges[j];
            if(!del[v]){
                for(ui k = p_pstart[v]; k < p_pstart[v+1]; k++){
                    ui w = p_edges[k];
                    if(!del[w] && mark[w] == 1 && w > v){
                        ++ sup_pp[u][v]; ++ sup_pp[v][u];
                        ++ sup_pp[u][w]; ++ sup_pp[w][u];
                        ++ sup_pp[v][w]; ++ sup_pp[w][v];
                    }
                }
                for(ui k = n_pstart[v]; k < n_pstart[v+1]; k++){
                    ui w = n_edges[k];
                    if(!del[w] && mark[w] == 2 && w > v){
                        ++ sup_nn[u][v]; ++ sup_nn[v][u];
                        ++ sup_np[u][w]; ++ sup_np[w][u];
                        ++ sup_np[v][w]; ++ sup_np[w][v];
                    }
                }
            }
        }
        for(ui j = n_pstart[u]; j < n_pstart[u+1]; j++){
            ui v = n_edges[j];
            if(!del[v]){
                for(ui k = p_pstart[v]; k < p_pstart[v+1]; k++){
                    ui w = p_edges[k];
                    if(!del[w] && mark[w] == 2 && w > v){
                        ++ sup_np[u][v]; ++ sup_np[v][u];
                        ++ sup_np[u][w]; ++ sup_np[w][u];
                        ++ sup_nn[v][w]; ++ sup_nn[w][v];
                    }
                }
                for(ui k = n_pstart[v]; k < n_pstart[v+1]; k++){
                    ui w = n_edges[k];
                    if(!del[w] && mark[w] == 1 && w > v){
                        ++ sup_np[u][v]; ++ sup_np[v][u];
                        ++ sup_np[v][w]; ++ sup_np[w][v];
                        ++ sup_nn[u][w]; ++ sup_nn[w][u];
                    }
                }
            }
        }
        for(ui j = p_pstart[u]; j < p_pstart[u+1]; j++) mark[p_edges[j]] = 0;
        for(ui j = n_pstart[u]; j < n_pstart[u+1]; j++) mark[n_edges[j]] = 0;
        del[u] = 1;
    }//u

    queue<pair<ui, ui>> Q;
    for(ui i = 0; i < n; i++){
        for(ui j = p_pstart[i]; j <p_pstart[i+1]; j++){
            ui v = p_edges[j];
            if(i < v){
                if(sup_pp[i][v] < tau - 2 || sup_nn[i][v] < tau){
                    Q.push(make_pair(i, v));
                }
            }
        }
        for(ui j = n_pstart[i]; j <n_pstart[i+1]; j++){
            ui v = n_edges[j];
            if(i < v){
                if(sup_np[i][v] < tau - 1){
                    Q.push(make_pair(i, v));
                }
            }
        }
    }

    while (!Q.empty()) {
        pair<ui, ui> te = Q.front();
        ++ dele_count;
        Q.pop();
        ui u = te.first;
        ui v = te.second;
        
#ifdef _DEBUG_
        cout<<"delete edge ( "<<u<<" , "<<v<<" ) from G."<<endl;
#endif
        
        if(e_sign[u][v] == 1){
            reord_deg(u, v);
            for(ui i = p_pstart[u]; i < p_pstart[u+1]; i++){
                ui w = p_edges[i];
                if(e_sign[v].find(w) != e_sign[v].end() && e_sign[v][w] == 1 && !e_del[u][w] && !e_del[v][w]){
                    if((sup_pp[u][w] --) == tau - 2 && sup_nn[u][w] >= tau)
                    {
                        Q.push(make_pair(u, w));
                    }
                    -- sup_pp[w][u];
                    if((sup_pp[v][w] --) == tau - 2 && sup_nn[v][w] >= tau)
                    {
                        Q.push(make_pair(v, w));
                    }
                    -- sup_pp[w][v];
                }
            }
            for(ui i = n_pstart[u]; i < n_pstart[u+1]; i++){
                ui w = n_edges[i];
                if(e_sign[v].find(w) != e_sign[v].end() && e_sign[v][w] == -1 && !e_del[u][w] && !e_del[v][w]){
                    if((sup_np[u][w] --) == tau - 1)
                    {
                        Q.push(make_pair(u, w));
                    }
                    -- sup_np[w][u];
                    if((sup_np[v][w] --) == tau - 1)
                    {
                        Q.push(make_pair(v, w));
                    }
                    -- sup_np[w][v];
                }
            }
        }
        else{
            reord_deg(u, v);
            for(ui i = p_pstart[u]; i < p_pstart[u+1]; i++){
                ui w = p_edges[i];
                if(e_sign[v].find(w) != e_sign[v].end() && e_sign[v][w] == -1 && !e_del[u][w] && !e_del[v][w]){
                    if((sup_nn[u][w] --) == tau && sup_pp[u][w] >= tau - 2)
                    {
                        Q.push(make_pair(u, w));
                    }
                    -- sup_nn[w][u];
                    if((sup_np[v][w] --) == tau - 1)
                    {
                        Q.push(make_pair(v, w));
                    }
                    -- sup_np[w][v];
                }
            }
            for(ui i = n_pstart[u]; i < n_pstart[u+1]; i++){
                ui w = n_edges[i];
                if(e_sign[v].find(w) != e_sign[v].end() && e_sign[v][w] == 1 && !e_del[u][w] && !e_del[v][w]){
                    if((sup_np[u][w] --) == tau - 1)
                    {
                        Q.push(make_pair(u, w));
                    }
                    -- sup_np[w][u];
                    if((sup_nn[v][w] --) == tau && sup_pp[v][w] >= tau - 2)
                    {
                        Q.push(make_pair(v, w));
                    }
                    -- sup_nn[w][v];
                }
            }
        }
        e_del[u][v] = 1;
        e_del[v][u] = 1;
    }
    
    delete [] vs;
    delete [] C;
    delete [] mark;
    delete [] del;
}

void shrink_on_reduced_e()
{
    for(ui i = 0; i < n; i++){
        p_pend[i] = p_pstart[i];
        n_pend[i] = n_pstart[i];
    }
    for(ui i = 0; i < n; i++){
        for(ui j = p_pstart[i]; j < p_pstart[i+1]; j++){
            ui u = p_edges[j]; //e(i,u)
            if(!e_del[i][u]){
                p_edges[p_pend[i]++] = u;
            }
        }
    }
    for(ui i = 0; i < n; i++){
        for(ui j = n_pstart[i]; j < n_pstart[i+1]; j++){
            ui u = n_edges[j]; //e(i,u)
            if(!e_del[i][u]){
                n_edges[n_pend[i]++] = u;
            }
        }
    }
    
    //update degree
    for(ui i = 0; i < n; i++){
        p_degree[i] = p_pend[i] - p_pstart[i];
        n_degree[i] = n_pend[i] - n_pstart[i];
        degree[i] = p_degree[i] + n_degree[i];
    }
    
#ifdef _DEBUG_
    cout<<"after shrink_on_reduced_e(), : "<<endl;
    for(ui i = 0; i < n; i++){
        cout<<"for vertex "<<i<<" : "<<endl;
        cout<<"  + neis : ";
        for(ui j = p_pstart[i]; j < p_pend[i]; j++){
            cout<<p_edges[j]<<", ";
        }cout<<endl;
        cout<<"  - neis : ";
        for(ui j = n_pstart[i]; j < n_pend[i]; j++){
            cout<<n_edges[j]<<", ";
        }cout<<endl;
    }
#endif
}

ui color_based_UB()
{
    ui max_color = 0;
    ui * color = new ui[n];
    for(ui i = 0; i < n; i++) color[i] = n;
    ui * vis = new ui[n];
    memset(vis, 0, sizeof(ui)*n);
    for(ui i = n; i > 0; i--){
        ui u = peel_s[i-1];
        for(ui j = p_pstart[u]; j < p_pend[u]; j++){
            ui c = color[p_edges[j]];
            if(c != n) {vis[c] = 1;}
        }
        for(ui j = n_pstart[u]; j < n_pend[u]; j++){
            ui c = color[n_edges[j]];
            if(c != n) {vis[c] = 1;}
        }
        for(ui j = 0; ;j++) if(!vis[j]) {
            color[u] = j;
            if(j > max_color) {max_color = j;}
            break;
        }
        for(ui j = p_pstart[u]; j < p_pend[u]; j++){
            ui c = color[p_edges[j]];
            if(c != n) vis[c] = 0;
        }
        for(ui j = n_pstart[u]; j < n_pend[u]; j++){
            ui c = color[n_edges[j]];
            if(c != n) vis[c] = 0;
        }
    }
    
    delete [] color;
    delete [] vis;
    
    return max_color + 1;
}

void PN_order()
{
    assert(n > 0);

    max_core = 0;
    ListLinearHeap *linear_heap = new ListLinearHeap(n, max_PorNdeg);
    linear_heap->init(n, max_PorNdeg, peel_s, PNdeg);
    core = new ui[n];
    memset(core, 0, sizeof(ui)*n);
    for(ui i = 0; i < n; i ++) {
        ui u, key;
        linear_heap->pop_min(u, key);
        if(key > max_core) max_core = key;
        peel_s[i] = u;
        core[u] = max_core;
        for(ui j = p_pstart[u];j < p_pend[u];j ++){
            ui v = p_edges[j];
            if(core[v] == 0){
                if((p_degree[v]--) < n_degree[v]){
                    linear_heap->decrement(v, 1);
                }
            }
        }
        for(ui j = n_pstart[u];j < n_pend[u];j ++){
            ui v = n_edges[j];
            if(core[v] == 0){
                if((n_degree[v]--) <= p_degree[v] + 1){
                    linear_heap->decrement(v, 1);
                }
            }
        }
    }
    delete linear_heap;
    
#ifdef _DEBUG_
    cout<<"core information : ";
    for(ui i = 0; i< n; i++) cout<<i<<": "<<core[i]<<",  ";cout<<endl;

    cout<<"peel sequence : ";
    for(ui i = 0; i< n; i++) cout<<peel_s[i]<<", "; cout<<endl;
#endif
}
   
void degeneracy_order()
{
    assert(n > 0);
    peel_s = new ui[n];
    for(ui i = 0; i < n; i++) peel_s[i] = i;
    max_core = 0;
    ListLinearHeap *linear_heap = new ListLinearHeap(n, n-1);
    linear_heap->init(n, n-1, peel_s, degree);
    core = new ui[n];
    memset(core, 0, sizeof(ui)*n);
    for(ui i = 0; i < n; i ++) {
        ui u, key;
        linear_heap->pop_min(u, key);
//        assert(key > 0);
        if(key > max_core) max_core = key;
        peel_s[i] = u;
        core[u] = max_core;
        for(ui j = p_pstart[u];j < p_pend[u];j ++) if(core[p_edges[j]] == 0)
            linear_heap->decrement(p_edges[j], 1);
        for(ui j = n_pstart[u];j < n_pend[u];j ++) if(core[n_edges[j]] == 0)
            linear_heap->decrement(n_edges[j], 1);
    }
    delete linear_heap;
    
#ifdef _DEBUG_
    cout<<"core information : ";
    for(ui i = 0; i< n; i++) cout<<i<<": "<<core[i]<<",  ";cout<<endl;
    cout<<"peel sequence : ";
    for(ui i = 0; i< n; i++) cout<<peel_s[i]<<", "; cout<<endl;
#endif
}

void shrink_and_orient_graph_Mtau_PNorder()
{
    ui threshold = Mtau + 1;
    ui * rid = new ui[n];
    for(ui i = 0; i < n; i ++) rid[peel_s[i]] = i;
    ui * mapping = new ui[n];
    ui * oldVid = new ui[n];
    ui idx = 0;
    for(ui i = 0; i < n; i++) if(core[peel_s[i]] >= threshold) {
        mapping[peel_s[i]] = idx;
        oldVid[idx] = peel_s[i];
        idx++;
    }
#ifdef _DEBUG_
    cout<<"in orient_graph(), mapping content : "<<endl;
    for(ui i = 0; i < n; i++){
        if(core[peel_s[i]] >= threshold){
            cout<<" "<<peel_s[i]<<" ---> "<<mapping[peel_s[i]]<<endl;
        }
    }
#endif
    p_pstart_o = new ui[n+1];
    p_edges_o = new ui[pm*2];
    p_pstart_o[0] = 0;
    ui cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = p_pstart_o[cnt];
            for(ui j = p_pstart[u]; j < p_pend[u]; j++){
                ui v = p_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    p_edges_o[pos++] = mapping[v];
                }
            }
            p_pstart_o[++cnt] = pos;
        }
    }
    assert(cnt == idx);
    
    n_pstart_o = new ui[n+1];
    n_edges_o = new ui[nm*2];
    n_pstart_o[0] = 0;
    cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = n_pstart_o[cnt];
            for(ui j = n_pstart[u]; j < n_pend[u]; j++){
                ui v = n_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    n_edges_o[pos++] = mapping[v];
                }
            }
            n_pstart_o[++cnt] = pos;
        }
    }
    assert(cnt == idx);
#ifdef _DEBUG_
    cout<<"after orient, n = "<<cnt<<endl;
    cout<<"p_pstart_o and p_pend_o info : "<<endl;
    for(ui i = 0; i < cnt; i++){
        cout<<"for vertex "<<i<<" : "<<endl;
        cout<<"  + neis : ";
        for(ui j = p_pstart_o[i]; j < p_pstart_o[i+1]; j++){
            cout<<p_edges_o[j]<<", ";
        }cout<<endl;
        cout<<"  - neis : ";
        for(ui j = n_pstart_o[i]; j < n_pstart_o[i+1]; j++){
            cout<<n_edges_o[j]<<", ";
        }cout<<endl;
    }
#endif
    n = idx;
    for(ui i = 0; i < n; i++) rid[i] = core[oldVid[i]];
    delete [] core;
    core = rid;
    delete [] mapping;
    delete [] oldVid;
}

void shrink_and_orient_graph_Mtau_dorder()
{
    ui threshold = Mtau + 1;
    ui * rid = new ui[n];
    memset(rid, 0, sizeof(ui)*n);
    for(ui i = 0; i < n; i ++) rid[peel_s[i]] = i;
    ui * mapping = new ui[n]; memset(mapping, 0, sizeof(ui)*n);
    ui * oldVid = new ui[n]; memset(oldVid, 0, sizeof(ui)*n);
    ui idx = 0;
    for(ui i = 0; i < n; i++) if(core[peel_s[i]] >= threshold) {
        mapping[peel_s[i]] = idx;
        oldVid[idx] = peel_s[i];
        idx++;
    }
#ifdef _DEBUG_
    cout<<"in orient_graph(), mapping content : "<<endl;
    for(ui i = 0; i < n; i++){
        if(core[peel_s[i]] >= threshold){
            cout<<" "<<peel_s[i]<<" ---> "<<mapping[peel_s[i]]<<endl;
        }
    }
#endif
    p_pstart_o = new ui[n+1];
    p_edges_o = new ui[pm*2];
    p_pstart_o[0] = 0;
    ui cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = p_pstart_o[cnt];
            for(ui j = p_pstart[u]; j < p_pend[u]; j++){
                ui v = p_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    p_edges_o[pos++] = mapping[v];
                }
            }
            p_pstart_o[++cnt] = pos;
        }
    }
    assert(cnt == idx);

    n_pstart_o = new ui[n+1];
    n_edges_o = new ui[nm*2];
    n_pstart_o[0] = 0;
    cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = n_pstart_o[cnt];
            for(ui j = n_pstart[u]; j < n_pend[u]; j++){
                ui v = n_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    n_edges_o[pos++] = mapping[v];
                }
            }
            n_pstart_o[++cnt] = pos;
        }
    }
    n = idx;
    for(ui i = 0; i < n; i++) rid[i] = core[oldVid[i]];
    delete [] core;
    core = rid;
    assert(cnt == idx);
    for(ui i = 1; i < n; i++) if(core[i] < core[i-1]) exit(1);
#ifdef _DEBUG_
    cout<<"after orient, n = "<<cnt<<endl;
    cout<<"p_pstart_o and p_pend_o info : "<<endl;
    for(ui i = 0; i < cnt; i++){
        cout<<"for vertex "<<i<<" : "<<endl;
        cout<<"  + neis : ";
        for(ui j = p_pstart_o[i]; j < p_pstart_o[i+1]; j++){
            cout<<p_edges_o[j]<<", ";
        }cout<<endl;
        cout<<"  - neis : ";
        for(ui j = n_pstart_o[i]; j < n_pstart_o[i+1]; j++){
            cout<<n_edges_o[j]<<", ";
        }cout<<endl;
    }
#endif
    delete [] mapping;
    delete [] oldVid;
}

void shrink_and_orient_graph()
{
    ui threshold = psz(cur_MC);
    ui * rid = new ui[n];
    for(ui i = 0; i < n; i ++) rid[peel_s[i]] = i;
    ui * mapping = new ui[n];
    ui * oldVid = new ui[n];
    
    ui idx = 0;
    for(ui i = 0; i < n; i++) if(core[peel_s[i]] >= threshold) {
        mapping[peel_s[i]] = idx;
        oldVid[idx] = peel_s[i];
        idx++;
    }
    
#ifdef _CaseStudy_
    ui * tmp_map = new ui[n];
    idx = 0;
    for(ui i = 0; i < n; i++) if(core[peel_s[i]] >= threshold) tmp_map[idx++] = ori_id[peel_s[i]];
    for(ui i = 0; i < idx; i++) ori_id[i] = tmp_map[i];
    delete [] tmp_map;
#endif
    
#ifdef _DEBUG_
    cout<<"in orient_graph(), mapping content : "<<endl;
    for(ui i = 0; i < n; i++){
        if(core[peel_s[i]] >= threshold){
            cout<<" "<<peel_s[i]<<" ---> "<<mapping[peel_s[i]]<<endl;
        }
    }
#endif
    p_pstart_o = new ui[n+1];
    p_edges_o = new ui[pm*2];
    p_pstart_o[0] = 0;
    ui cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = p_pstart_o[cnt];
            for(ui j = p_pstart[u]; j < p_pend[u]; j++){
                ui v = p_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    p_edges_o[pos++] = mapping[v];
                }
            }
            p_pstart_o[++cnt] = pos;
        }
    }
    assert(cnt == idx);

    
    n_pstart_o = new ui[n+1];
    n_edges_o = new ui[nm*2];
    n_pstart_o[0] = 0;
    cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = n_pstart_o[cnt];
            for(ui j = n_pstart[u]; j < n_pend[u]; j++){
                ui v = n_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    n_edges_o[pos++] = mapping[v];
                }
            }
            n_pstart_o[++cnt] = pos;
        }
    }
    assert(cnt == idx);
#ifdef _DEBUG_
    cout<<"after orient, n = "<<cnt<<endl;
    cout<<"p_pstart_o and p_pend_o info : "<<endl;
    for(ui i = 0; i < cnt; i++){
        cout<<"for vertex "<<i<<" : "<<endl;
        cout<<"  + neis : ";
        for(ui j = p_pstart_o[i]; j < p_pstart_o[i+1]; j++){
            cout<<p_edges_o[j]<<", ";
        }cout<<endl;
        cout<<"  - neis : ";
        for(ui j = n_pstart_o[i]; j < n_pstart_o[i+1]; j++){
            cout<<n_edges_o[j]<<", ";
        }cout<<endl;
    }
#endif
    n = idx;
    for(ui i = 0; i < n; i++) rid[i] = core[oldVid[i]];
    delete [] core;
    core = rid;
    delete [] mapping;
    delete [] oldVid;
}

void construct_induced_subgraph(ui * vsP, ui vsP_size, ui * vsN, ui vsN_size, ui & tmp_ori_edges, ui& tmp_now_edges)
{
    tmp_ori_edges = vsP_size + vsN_size;
    tmp_now_edges = 0;
    for(ui i = 0; i < vsP_size; i++) {
        ui u = vsP[i];
        degree[u] = 0;
        p_degree[u] = 0;
        n_degree[u] = 0;
    }
    for(ui i = 0; i < vsN_size; i++) {
        ui u = vsN[i];
        degree[u] = 0;
        p_degree[u] = 0;
        n_degree[u] = 0;
    }
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 1){
                ++ degree[u];
                ++ degree[v];
                ++ p_degree[u];
                ++ p_degree[v];
                ++ tmp_now_edges;
            }
            if(inPN[v] != 0) ++ tmp_ori_edges;
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 2){
                ++ degree[u];
                ++ degree[v];
                ++ n_degree[u];
                ++ n_degree[v];
                ++ tmp_now_edges;
            }
            if(inPN[v] != 0) ++ tmp_ori_edges;
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 2){
                ++ degree[u];
                ++ degree[v];
                ++ p_degree[u];
                ++ p_degree[v];
                ++tmp_now_edges;
            }
            if(inPN[v] != 0) ++ tmp_ori_edges;
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 1){
                ++ degree[u];
                ++ degree[v];
                ++ n_degree[u];
                ++ n_degree[v];
                ++tmp_now_edges;
            }
            if(inPN[v] != 0) ++ tmp_ori_edges;
        }
    }
    
#ifdef _DEBUG_
    cout<<"in this induced subgraph, each vertex degree : "<<endl;
    for(ui i = 0; i < vsP_size; i++)
        cout<<vsP[i]<<": deg = "<<degree[vsP[i]]<<",  p_deg = "<<p_degree[vsP[i]]<<",  n_deg = "<<n_degree[vsP[i]]<<endl;
    for(ui i = 0; i < vsN_size; i++)
        cout<<vsN[i]<<": deg = "<<degree[vsN[i]]<<",  p_deg = "<<p_degree[vsN[i]]<<",  n_deg = "<<n_degree[vsN[i]]<<endl;
#endif
    
    assert(vsP_size > 0);
    assert(vsN_size > 0);
    
    p_pstart[vsP[0]] = 0;
    for(ui i = 1; i < vsP_size; i++) p_pstart[vsP[i]] = p_pstart[vsP[i-1]] + p_degree[vsP[i-1]];
    if(vsP_size > 0) p_pstart[vsN[0]] = p_pstart[vsP[vsP_size-1]] + p_degree[vsP[vsP_size-1]];
    else p_pstart[vsN[0]] = 0;
    for(ui i = 1; i < vsN_size; i++) p_pstart[vsN[i]] = p_pstart[vsN[i-1]] + p_degree[vsN[i-1]];
    
    n_pstart[vsP[0]] = 0;
    for(ui i = 1; i < vsP_size; i++) n_pstart[vsP[i]] = n_pstart[vsP[i-1]] + n_degree[vsP[i-1]];
    if(vsP_size > 0) n_pstart[vsN[0]] = n_pstart[vsP[vsP_size-1]] + n_degree[vsP[vsP_size-1]];
    else n_pstart[vsN[0]] = 0;
    for(ui i = 1; i < vsN_size; i++) n_pstart[vsN[i]] = n_pstart[vsN[i-1]] + n_degree[vsN[i-1]];
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        p_pend[u] = p_pstart[u];
        n_pend[u] = n_pstart[u];
    }
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        p_pend[u] = p_pstart[u];
        n_pend[u] = n_pstart[u];
    }
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 1){
                p_edges[p_pend[u]++] = v;
                p_edges[p_pend[v]++] = u;
            }
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 2){
                n_edges[n_pend[u]++] = v;
                n_edges[n_pend[v]++] = u;
            }
        }
    }
    
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 2){
                p_edges[p_pend[u]++] = v;
                p_edges[p_pend[v]++] = u;
            }
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 1){
                n_edges[n_pend[u]++] = v;
                n_edges[n_pend[v]++] = u;
            }
        }
    }
}

void vs_vertex_reduce_Mtau(ui * vsP, ui & vsP_size, ui * vsN, ui & vsN_size)
{
    int vsP_pt = Mtau - 1;
    int vsP_nt = Mtau + 1;
    
    int vsN_pt = Mtau;
    int vsN_nt = Mtau;
    
    queue<ui> Q;
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        if(p_degree[u] < vsP_pt || n_degree[u] < vsP_nt){
            Q.push(u);
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        if(p_degree[u] < vsN_pt || n_degree[u] < vsN_nt){
            Q.push(u);
        }
    }
    
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        assert(inPN[u]==1 || inPN[u]==2);
        degree[u] = 0;
        p_degree[u] = 0;
        n_degree[u] = 0;

        for(ui i = p_pstart[u]; i < p_pend[u]; i++){
            ui v = p_edges[i];
            if(p_degree[v] > 0){
                assert(inPN[u] == inPN[v]);
                if(inPN[v] == 1){
                    if((p_degree[v]--) == vsP_pt && n_degree[v] >= vsP_nt){
                        Q.push(v);
                    }
                }
                else{
                    if((p_degree[v]--) == vsN_pt && n_degree[v] >= vsN_nt){
                        Q.push(v);
                    }
                }
            }
        }
        for(ui i = n_pstart[u]; i < n_pend[u]; i++){
            ui v = n_edges[i];
            if(n_degree[v] > 0){
                assert(inPN[u] != inPN[v]);
                if(inPN[v] == 1){
                    if((n_degree[v]--) == vsP_nt && p_degree[v] >= vsP_pt){
                        Q.push(v);
                    }
                }
                else{
                    if((n_degree[v]--) == vsN_nt && p_degree[v] >= vsN_pt){
                        Q.push(v);
                    }
                }
            }
        }
        inPN[u] = 0;
    }
    ui vsP_new_size = 0, vsN_new_size = 0;
    for(ui i = 0; i < vsP_size; i++){
        if(inPN[vsP[i]] != 0){
            vsP[vsP_new_size++] = vsP[i];
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        if(inPN[vsN[i]] != 0){
            vsN[vsN_new_size++] = vsN[i];
        }
    }
    vsP_size = vsP_new_size;
    vsN_size = vsN_new_size;
    //update degree
    for(ui i = 0; i < vsP_size; i++)
        degree[vsP[i]] = p_degree[vsP[i]] + n_degree[vsP[i]];
    for(ui i = 0; i < vsN_size; i++)
        degree[vsN[i]] = p_degree[vsN[i]] + n_degree[vsN[i]];
    
#ifdef _DEBUG_
    cout<<"now, vsP_new_size = "<<vsP_new_size<<endl;
    cout<<"now, vsN_new_size = "<<vsN_new_size<<endl;
    
    cout<<"vsP : "; for(ui i = 0; i < vsP_size; i++) cout<<vsP[i]<<", ";cout<<endl;
    cout<<"vsN : "; for(ui i = 0; i < vsN_size; i++) cout<<vsN[i]<<", ";cout<<endl;
#endif
    
}

void vs_vertex_reduce(ui * vsP, ui & vsP_size, ui * vsN, ui & vsN_size)
{
    int vsP_pt = tau - 2;
    int vsP_nt = tau;
    
    int vsN_pt = tau - 1;
    int vsN_nt = tau - 1;
    
    queue<ui> Q;
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        if(p_degree[u] < vsP_pt || n_degree[u] < vsP_nt){
            Q.push(u);
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        if(p_degree[u] < vsN_pt || n_degree[u] < vsN_nt){
            Q.push(u);
        }
    }
    
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        assert(inPN[u]==1 || inPN[u]==2);
        degree[u] = 0;
        p_degree[u] = 0;
        n_degree[u] = 0;

        for(ui i = p_pstart[u]; i < p_pend[u]; i++){
            ui v = p_edges[i];
            if(p_degree[v] > 0){
                assert(inPN[u] == inPN[v]);
                if(inPN[v] == 1){
                    if((p_degree[v]--) == vsP_pt && n_degree[v] >= vsP_nt){
                        Q.push(v);
                    }
                }
                else{
                    if((p_degree[v]--) == vsN_pt && n_degree[v] >= vsN_nt){
                        Q.push(v);
                    }
                }
            }
        }
        for(ui i = n_pstart[u]; i < n_pend[u]; i++){
            ui v = n_edges[i];
            if(n_degree[v] > 0){
                assert(inPN[u] != inPN[v]);
                if(inPN[v] == 1){
                    if((n_degree[v]--) == vsP_nt && p_degree[v] >= vsP_pt){
                        Q.push(v);
                    }
                }
                else{
                    if((n_degree[v]--) == vsN_nt && p_degree[v] >= vsN_pt){
                        Q.push(v);
                    }
                }
            }
        }
        inPN[u] = 0;
    }
    ui vsP_new_size = 0, vsN_new_size = 0;
    for(ui i = 0; i < vsP_size; i++){
        if(inPN[vsP[i]] != 0){
            vsP[vsP_new_size++] = vsP[i];
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        if(inPN[vsN[i]] != 0){
            vsN[vsN_new_size++] = vsN[i];
        }
    }
    vsP_size = vsP_new_size;
    vsN_size = vsN_new_size;
    //update degree
    for(ui i = 0; i < vsP_size; i++)
        degree[vsP[i]] = p_degree[vsP[i]] + n_degree[vsP[i]];
    for(ui i = 0; i < vsN_size; i++)
        degree[vsN[i]] = p_degree[vsN[i]] + n_degree[vsN[i]];
    
#ifdef _DEBUG_
    cout<<"after ve_vertex_reduction."<<endl;
    cout<<"now, vsP_new_size = "<<vsP_new_size<<"  :  "; for(ui i = 0; i < vsP_size; i++) cout<<vsP[i]<<", ";cout<<endl;
    cout<<"now, vsN_new_size = "<<vsN_new_size<<"  :  "; for(ui i = 0; i < vsN_size; i++) cout<<vsN[i]<<", ";cout<<endl;
#endif
    
}

void reduce_to_kcore(ui * vsP, ui & vsP_size, ui * vsN, ui & vsN_size, int k)
{
    queue<ui> Q;
    for(ui i = 0; i < vsP_size; i++){
        if(degree[vsP[i]] < k){
            Q.push(vsP[i]);
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        if(degree[vsN[i]] < k){
            Q.push(vsN[i]);
        }
    }
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        inPN[u] = 0;
        degree[u] = 0;
        for(ui i = p_pstart[u]; i < p_pend[u]; i++){
            ui v = p_edges[i];
            if(degree[v] > 0){
                if((degree[v]--) == k){
                    Q.push(v);
                }
            }
        }
        for(ui i = n_pstart[u]; i < n_pend[u]; i++){
            ui v = n_edges[i];
            if(degree[v] > 0){
                if((degree[v]--) == k){
                    Q.push(v);
                }
            }
        }
    }
    ui vsP_new_size = 0, vsN_new_size = 0;
    for(ui i = 0; i < vsP_size; i++){
        if(inPN[vsP[i]] != 0){
            vsP[vsP_new_size++] = vsP[i];
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        if(inPN[vsN[i]] != 0){
            vsN[vsN_new_size++] = vsN[i];
        }
    }
    
    vsP_size = vsP_new_size;
    vsN_size = vsN_new_size;
    
#ifdef _DEBUG_
    cout<<"after reduce_to_kcore."<<endl;
    cout<<"now, vsP_new_size = "<<vsP_new_size<<"  :  "; for(ui i = 0; i < vsP_size; i++) cout<<vsP[i]<<", ";cout<<endl;
    cout<<"now, vsN_new_size = "<<vsN_new_size<<"  :  "; for(ui i = 0; i < vsN_size; i++) cout<<vsN[i]<<", ";cout<<endl;
#endif

}

void get_degeneracy_order(ui * vs, ui vs_size)
{
    ui cur_max_coreunm = 0;
    for(ui i = 0; i < vs_size; i++) {
        ui idx = i;
        for(ui j = i+1; j < vs_size; j++){
            if(degree[vs[j]] < degree[vs[idx]]){
                idx = j;
            }
        }
        if(idx != i){
            swap(vs[idx], vs[i]);
        }
        ui u = vs[i];
        if(degree[u] > cur_max_coreunm)
            cur_max_coreunm = degree[u];
        vs_core[u] = cur_max_coreunm;
        for(ui j = i+1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] != 0){
                assert(degree[u] > 0);
                assert(degree[v] > 0);
                -- degree[u];
                -- degree[v];
            }
        }
    }
#ifdef _DEBUG_
    cout<<"after comp_corenum(), peel sequence and core number for each vertex : "<<endl;
    for(ui i = 0; i < vs_size; i++)
        cout<<vs[i]<<":"<<vs_core[vs[i]]<<", ";
    cout<<endl;
#endif
}

void comp_corenum_and_reduce_to_kcore_by_Matrix(ui * vs, ui & vs_size, int k)
{
    assert(k >= 0);
    ui cur_max_coreunm = 0;
    for(ui i = 0; i < vs_size; i++) {
        ui idx = i;
        for(ui j = i+1; j < vs_size; j++){
            if(degree[vs[j]] < degree[vs[idx]]){
                idx = j;
            }
        }
        if(idx != i){
            swap(vs[idx], vs[i]);
        }
        ui u = vs[i];
        if(degree[u] > cur_max_coreunm)
            cur_max_coreunm = degree[u];
        vs_core[u] = cur_max_coreunm;
        for(ui j = i+1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] != 0){
                assert(degree[u] > 0);
                assert(degree[v] > 0);
                -- degree[u];
                -- degree[v];
            }
        }
    }
#ifdef _DEBUG_
    cout<<"after comp_corenum(), peel sequence and core number for each vertex : "<<endl;
    for(ui i = 0; i < vs_size; i++)
        cout<<vs[i]<<":"<<vs_core[vs[i]]<<", ";
    cout<<endl;
#endif
    
    ui new_vs_size = 0;
    for(ui i = 0; i < vs_size; i++){
        if(vs_core[vs[i]] >= k){
            vs[new_vs_size++] = vs[i];
        }
    }
    vs_size = new_vs_size;
#ifdef _DEBUG_
    cout<<"after reduce_to_kcore(), peel sequence and core number for each vertex : "<<endl;
    for(ui i = 0; i < vs_size; i++)
        cout<<vs[i]<<":"<<vs_core[vs[i]]<<", ";
    cout<<endl;
#endif
}

//vs_core
void comp_corenum_and_reduce_to_kcore_by_Matrix(ui * vs, ui & vs_size, int k, ui & suffix_len)
{
    suffix_len = 0;
    ui cur_max_coreunm = 0;
    for(ui i = 0; i < vs_size; i++) {
        ui idx = i;
        for(ui j = i+1; j < vs_size; j++){
            if(degree[vs[j]] < degree[vs[idx]]){
                idx = j;
            }
        }
        if(idx != i){
            swap(vs[idx], vs[i]);
        }
        ui u = vs[i];
        if(degree[u] > cur_max_coreunm)
            cur_max_coreunm = degree[u];
        vs_core[u] = cur_max_coreunm;
        
        if(degree[u] + i + 1 == vs_size){
            suffix_len = 1;
            for(ui j = i+1; j < vs_size; j++){
                vs_core[vs[j]] = cur_max_coreunm;
                suffix_len ++;
            }
            break;
        }
        
        for(ui j = i+1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] != 0){
                assert(degree[u] > 0);
                assert(degree[v] > 0);
                -- degree[u];
                -- degree[v];
            }
        }
    }
#ifdef _DEBUG_
    cout<<"after comp_corenum(), peel sequence and core number for each vertex : "<<endl;
    for(ui i = 0; i < vs_size; i++)
        cout<<vs[i]<<":"<<vs_core[vs[i]]<<", ";
    cout<<endl;
#endif
    
    ui new_vs_size = 0;
    for(ui i = 0; i < vs_size; i++){
        if(vs_core[vs[i]] >= k){
            vs[new_vs_size++] = vs[i];
        }
    }
    assert(new_vs_size <= vs_size);
    vs_size = new_vs_size;
#ifdef _DEBUG_
    cout<<"after reduce_to_kcore(), peel sequence and core number for each vertex : "<<endl;
    for(ui i = 0; i < vs_size; i++)
        cout<<vs[i]<<":"<<vs_core[vs[i]]<<", ";
    cout<<endl;
#endif
    //set suffix_idx
    if(vs_size < suffix_len)
        suffix_len = 0;
}

void get_higher_neighbors(ui u, ui * vsP, ui &vsP_size, ui * vsN, ui &vsN_size)
{
    memset(inPN, 0, sizeof(ui)*n);
    vsP_size = 0;
    for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
        vsP[vsP_size++] = p_edges_o[j];
        inPN[p_edges_o[j]] = 1;
    }
    vsN_size = 0;
    for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
        vsN[vsN_size++] = n_edges_o[j];
        inPN[n_edges_o[j]] = 2;
    }
}

void construct_Matrix(ui * vsP, ui vsP_size, ui * vsN, ui vsN_size)
{
    ui idx = 0;
    for(ui i = 0; i < vsP_size; i++){
        trans[vsP[i]] = idx ++;
    }
    for(ui i = 0; i < vsN_size; i++){
        trans[vsN[i]] = idx ++;
    }
    
    assert(idx == (vsP_size + vsN_size));
    
    for(ui i = 0; i < idx; i++)
        for(ui j = 0; j < idx; j++)
            Matrix[i][j] = 0;
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 1){
                Matrix[trans[u]][trans[v]] = 1;
                Matrix[trans[v]][trans[u]] = 1;
            }
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 2){
                Matrix[trans[u]][trans[v]] = -1;
                Matrix[trans[v]][trans[u]] = -1;
            }
        }
    }
    
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 2){
                Matrix[trans[u]][trans[v]] = 1;
                Matrix[trans[v]][trans[u]] = 1;
            }
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[n_edges_o[j]] == 1){
                Matrix[trans[u]][trans[v]] = -1;
                Matrix[trans[v]][trans[u]] = -1;
            }
        }
    }
}

void construct_Matrix_without_ce(ui * vsP, ui vsP_size, ui * vsN, ui vsN_size)
{
    ui idx = 0;
    for(ui i = 0; i < vsP_size; i++){
        trans[vsP[i]] = idx ++;
    }
    for(ui i = 0; i < vsN_size; i++){
        trans[vsN[i]] = idx ++;
    }
    
    assert(idx == (vsP_size + vsN_size));
    
    for(ui i = 0; i < idx; i++)
        for(ui j = 0; j < idx; j++)
            Matrix[i][j] = 0;
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 1 || inPN[v] == 2){
                Matrix[trans[u]][trans[v]] = 1;
                Matrix[trans[v]][trans[u]] = 1;
            }
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 2 || inPN[v] == 1){
                Matrix[trans[u]][trans[v]] = -1;
                Matrix[trans[v]][trans[u]] = -1;
            }
        }
    }
    
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 2 || inPN[v] == 1){
                Matrix[trans[u]][trans[v]] = 1;
                Matrix[trans[v]][trans[u]] = 1;
            }
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 1 || inPN[v] == 2){
                Matrix[trans[u]][trans[v]] = -1;
                Matrix[trans[v]][trans[u]] = -1;
            }
        }
    }
}

void obtain_degree_Mtau(ui * vs, ui vs_size)
{
    for(ui i = 0; i < vs_size; i++){
        ui u = vs[i];
        degree[u] = 0;
        p_degree[u] = 0;
        n_degree[u] = 0;
    }
    for(ui i = 0; i < vs_size; i++){
        ui u = vs[i];
        for(ui j = i + 1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] == 1){
                ++ degree[u]; ++ degree[v];
                ++ p_degree[u]; ++ p_degree[v];
            }
            else if(Matrix[trans[u]][trans[v]] == -1){
                ++ degree[u]; ++ degree[v];
                ++ n_degree[u]; ++ n_degree[v];
            }
        }
    }
    
#ifdef _DEBUG_
    cout<<"each vertex degree by obtain_degree(): "<<endl;
    for(ui i = 0; i < vs_size; i++){
        cout<<"vertex "<<vs[i]<<": degree = "<<degree[vs[i]]<<", p_degree = "<<p_degree[vs[i]]<<", n_degree = "<<n_degree[vs[i]]<<endl;
    }
    cout<<endl;
#endif
}

void obtain_degree(ui * vs, ui vs_size)
{
    for(ui i = 0; i < vs_size; i++) degree[vs[i]] = 0;
    for(ui i = 0; i < vs_size; i++){
        ui u = vs[i];
        for(ui j = i + 1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] != 0){
                ++ degree[u];
                ++ degree[v];
            }
        }
    }
#ifdef _DEBUG_
    cout<<"each vertex degree by obtain_degree(): ";
    for(ui i = 0; i < vs_size; i++)
        cout<<degree[vs[i]]<<",";
    cout<<endl;
#endif
}

ui degeneracy_order_on_Matrix(vector<ui> & vs)
{
    ui cur_core_num = 0;
    for(ui i = 0; i < vs.size(); i++){
        ui idx = i;
        for(ui j = i+1; j < vs.size(); j++){
            if(degree[vs[j]] < degree[vs[i]])
                idx = j;
        }
        if(idx != i) swap(vs[idx], vs[i]);
        ui u = vs[i]; // u has min degree
        if(degree[u] > cur_core_num) cur_core_num = degree[u];
        vs_core[u] = cur_core_num;
        for(ui j = i+1; j < vs.size(); j++){
            if(Matrix[trans[u]][trans[vs[j]]] == 1 || Matrix[trans[u]][trans[vs[j]]] == -1){
                -- degree[u];
                -- degree[vs[j]];
            }
        }
    }
    return cur_core_num;
}

void shrink_vs(vector<ui> & vs, ui & vs_size, int threshold)
{
    for(ui i = 0; i < vs.size(); i++){
        if(vs_core[vs[i]] >= threshold){
            vs[vs_size++] = vs[i];
        }
    }
}

ui color_based_UB_Matrix(ui * vs, ui vs_size)
{
    ui max_color = 0;
    for(ui i = 0; i < vs_size; i++){
        vs_color[vs[i]] = vs_size;
    }
    ui * vis = new ui[vs_size];
    memset(vis, 0, sizeof(ui)*vs_size);
    for(ui i = vs_size; i > 0; i--){
        ui u = vs[i-1];
        for(ui j = vs_size; j > 0; j--){
            ui v = vs[j-1];
            if(u == v) continue;
            if(Matrix[trans[u]][trans[v]] == 1 || Matrix[trans[u]][trans[v]] == -1){
                ui c = vs_color[v];
                if(c != vs_size) {vis[c] = 1;}
            }
        }
        for(ui j = 0;; j++){
            if(!vis[j]){
                vs_color[u] = j;
                if(j > max_color) max_color = j;
                break;
            }
        }
        for(ui j = vs_size; j > 0; j--){
            ui v = vs[j-1];
            if(u == v) continue;
            if(Matrix[trans[u]][trans[v]] == 1 || Matrix[trans[u]][trans[v]] == -1){
                ui c = vs_color[v];
                if(c != vs_size) {vis[c] = 0;}
            }
        }
    }
    assert(max_color < vs_size);
    delete [] vis;
    return max_color+1;
}

void mDC_for_BF_Bin(pair<vector<ui>, vector<ui>> cur_C, ui * vs, ui vs_size, int tp, int tn)
{
    if(psz(cur_MC) != 0) return;
    
    if(tp == 0 && tn == 0){
        cur_MC = cur_C; return;
    }
    
    if(psz(cur_C) + vs_size <= psz(cur_MC)) return;
    
    obtain_degree(vs, vs_size);

    ui suffix_len;
    comp_corenum_and_reduce_to_kcore_by_Matrix(vs, vs_size, mav(psz(cur_MC) + 1 - psz(cur_C) - 1, 0), suffix_len);
    assert(suffix_len >= 0 && suffix_len <= vs_size);
    if(vs_size == 0) return;
    
    pair<vector<ui>, vector<ui>> sfx_C(cur_C);
    for(ui i = vs_size - suffix_len; i < vs_size; i++){
        ui u = vs[i];
        assert(inPN[u] == 1 || inPN[u] == 2);
        if(inPN[u] == 1) sfx_C.first.push_back(u);
        else sfx_C.second.push_back(u);
    }
    if(sfx_C.first.size() >= tau && sfx_C.second.size() >= tau && psz(sfx_C) > psz(cur_MC)) cur_MC = sfx_C;
    
    int coUB = color_based_UB_Matrix(vs, vs_size);
    if(coUB < mav(psz(cur_MC) + 1 - psz(cur_C), 0)) return;
    
    int p_cand = 0, n_cand = 0;
    for(ui i = 0; i < vs_size; i++){
        assert(inPN[vs[i]] == 1 || inPN[vs[i]] == 2);
        if(inPN[vs[i]] == 1) ++ p_cand;
        else ++ n_cand;
    }
    if(p_cand < tp || n_cand < tn) return;
    
    if(tp > 0  && tn > 0){
        assert(p_cand > 0); assert(n_cand > 0);
        if(p_cand <= n_cand){ // first select from P
            vector<ui> tmpvec(vs_size);
            for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
            ui n_idx = 0;
            ui p_idx = n_cand;
            for(ui i = 0; i < vs_size; i++){
                ui u = tmpvec[i];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) vs[p_idx++] = u;
                else vs[n_idx++] = u;
            }
            assert(p_idx == vs_size); assert(n_idx == n_cand);

            vector<int> pivot_indicator(vs_size, 1);
            vector<int> exp_indicator(vs_size, 1);
            
            bool pivot_f = true;
            for(ui i = vs_size; i > 0; i--){
                ui u = vs[i-1];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 2) continue;
                if(pivot_indicator[i-1] == 0) continue;
                if(pivot_f){
                    for(ui j = 0; j < vs_size; j++){
                        ui v = vs[j];
                        if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                    }
                    pivot_f = false;
                }
                vector<ui> next_g;
                for(ui j = vs_size; j > 0; j--){
                    ui v = vs[j-1];
                    if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
                }
                pair<vector<ui>, vector<ui>> next_C(cur_C);
                int new_tp, new_tn;
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1){
                    new_tp = mav(tp-1, 0);
                    new_tn = tn;
                    next_C.first.push_back(u);
                }
                else{
                    new_tp = tp;
                    new_tn = mav(tn-1, 0);
                    next_C.second.push_back(u);
                }
                mDC_for_BF_Bin(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
                exp_indicator[i-1] = 0;
            }
        }
        else{ // first select from N
            vector<ui> tmpvec(vs_size);
            for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
            ui n_idx = p_cand;
            ui p_idx = 0;
            for(ui i = 0; i < vs_size; i++){
                ui u = tmpvec[i];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) vs[p_idx++] = u;
                else vs[n_idx++] = u;
            }
            assert(p_idx == p_cand); assert(n_idx == vs_size);

            vector<int> pivot_indicator(vs_size, 1);
            vector<int> exp_indicator(vs_size, 1);
            
            bool pivot_f = true;
            for(ui i = vs_size; i > 0; i--){
                ui u = vs[i-1];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) continue;
                if(pivot_indicator[i-1] == 0) continue;
                
                if(pivot_f){
                    for(ui j = 0; j < vs_size; j++){
                        ui v = vs[j];
                        if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                    }
                    pivot_f = false;
                }
                
                vector<ui> next_g;
                for(ui j = vs_size; j > 0; j--){
                    ui v = vs[j-1];
                    if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
                }
                
                pair<vector<ui>, vector<ui>> next_C(cur_C);
                int new_tp, new_tn;
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1){
                    new_tp = mav(tp-1, 0);
                    new_tn = tn;
                    next_C.first.push_back(u);
                }
                else{
                    new_tp = tp;
                    new_tn = mav(tn-1, 0);
                    next_C.second.push_back(u);
                }
                mDC_for_BF_Bin(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
                exp_indicator[i-1] = 0;
            }
        }
    }
    else if (tp > 0 && tn == 0){
        vector<ui> tmpvec(vs_size);
        for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
        ui n_idx = 0;
        ui p_idx = n_cand;
        for(ui i = 0; i < vs_size; i++){
            ui u = tmpvec[i];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) vs[p_idx++] = u;
            else vs[n_idx++] = u;
        }
        assert(p_idx == vs_size); assert(n_idx == n_cand);
        
        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        bool pivot_f = true;
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 2) continue;
            if(pivot_indicator[i-1] == 0) continue;
            if(pivot_f){
                for(ui j = 0; j < vs_size; j++){
                    ui v = vs[j];
                    if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                }
                pivot_f = false;
            }
//            cout<<"next will expand vertex "<<u<<endl;
            
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
            }
            
            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            mDC_for_BF_Bin(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
    else if (tp == 0 && tn > 0){
        vector<ui> tmpvec(vs_size);
        for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
        ui n_idx = p_cand;
        ui p_idx = 0;
        for(ui i = 0; i < vs_size; i++){
            ui u = tmpvec[i];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) vs[p_idx++] = u;
            else vs[n_idx++] = u;
        }
        assert(p_idx == p_cand); assert(n_idx == vs_size);

        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        bool pivot_f = true;
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) continue;
            if(pivot_indicator[i-1] == 0) continue;
            if(pivot_f){
                for(ui j = 0; j < vs_size; j++){
                    ui v = vs[j];
                    if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                }
                pivot_f = false;
            }
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
            }

            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            mDC_for_BF_Bin(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
    else{
        cout<<"wrong !!"<<endl;
        exit(1);
    }
}

void mDC(pair<vector<ui>, vector<ui>> cur_C, ui * vs, ui vs_size, int tp, int tn)
{
    if(vs_size == 0 && tp == 0 && tn == 0){
        if(psz(cur_C) > psz(cur_MC)) cur_MC = cur_C; return;
    }
    
    if(psz(cur_C) + vs_size <= psz(cur_MC)) return;
    
    obtain_degree(vs, vs_size);

    ui suffix_len;
    comp_corenum_and_reduce_to_kcore_by_Matrix(vs, vs_size, mav(psz(cur_MC) + 1 - psz(cur_C) - 1, 0), suffix_len);
    assert(suffix_len >= 0 && suffix_len <= vs_size);
    if(vs_size == 0) return;
    
    pair<vector<ui>, vector<ui>> sfx_C(cur_C);
    for(ui i = vs_size - suffix_len; i < vs_size; i++){
        ui u = vs[i];
        assert(inPN[u] == 1 || inPN[u] == 2);
        if(inPN[u] == 1) sfx_C.first.push_back(u);
        else sfx_C.second.push_back(u);
    }
    if(sfx_C.first.size() >= tau && sfx_C.second.size() >= tau && psz(sfx_C) > psz(cur_MC)) cur_MC = sfx_C;
    
#ifdef _COLORUB_
    int coUB = color_based_UB_Matrix(vs, vs_size);
    if(coUB < mav(psz(cur_MC) + 1 - psz(cur_C), 0)) return;
#endif
    
    int p_cand = 0, n_cand = 0;
    for(ui i = 0; i < vs_size; i++){
        assert(inPN[vs[i]] == 1 || inPN[vs[i]] == 2);
        if(inPN[vs[i]] == 1) ++ p_cand;
        else ++ n_cand;
    }
    if(p_cand < tp || n_cand < tn) return;
    
    if(tp > 0  && tn > 0){
        assert(p_cand > 0); assert(n_cand > 0);
        if(p_cand <= n_cand){ // first select from P
            vector<ui> tmpvec(vs_size);
            for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
            ui n_idx = 0;
            ui p_idx = n_cand;
            for(ui i = 0; i < vs_size; i++){
                ui u = tmpvec[i];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) vs[p_idx++] = u;
                else vs[n_idx++] = u;
            }
            assert(p_idx == vs_size); assert(n_idx == n_cand);

            vector<int> pivot_indicator(vs_size, 1);
            vector<int> exp_indicator(vs_size, 1);
            
            bool pivot_f = true;
            for(ui i = vs_size; i > 0; i--){
                ui u = vs[i-1];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 2) continue;
                if(pivot_indicator[i-1] == 0) continue;
                if(pivot_f){
                    for(ui j = 0; j < vs_size; j++){
                        ui v = vs[j];
                        if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                    }
                    pivot_f = false;
                }
                vector<ui> next_g;
                for(ui j = vs_size; j > 0; j--){
                    ui v = vs[j-1];
                    if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
                }
                pair<vector<ui>, vector<ui>> next_C(cur_C);
                int new_tp, new_tn;
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1){
                    new_tp = mav(tp-1, 0);
                    new_tn = tn;
                    next_C.first.push_back(u);
                }
                else{
                    new_tp = tp;
                    new_tn = mav(tn-1, 0);
                    next_C.second.push_back(u);
                }
                mDC(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
                exp_indicator[i-1] = 0;
            }
        }
        else{ // first select from N
            vector<ui> tmpvec(vs_size);
            for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
            ui n_idx = p_cand;
            ui p_idx = 0;
            for(ui i = 0; i < vs_size; i++){
                ui u = tmpvec[i];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) vs[p_idx++] = u;
                else vs[n_idx++] = u;
            }
            assert(p_idx == p_cand); assert(n_idx == vs_size);

            vector<int> pivot_indicator(vs_size, 1);
            vector<int> exp_indicator(vs_size, 1);
            
            bool pivot_f = true;
            for(ui i = vs_size; i > 0; i--){
                ui u = vs[i-1];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) continue;
                if(pivot_indicator[i-1] == 0) continue;
                
                if(pivot_f){
                    for(ui j = 0; j < vs_size; j++){
                        ui v = vs[j];
                        if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                    }
                    pivot_f = false;
                }
                
                vector<ui> next_g;
                for(ui j = vs_size; j > 0; j--){
                    ui v = vs[j-1];
                    if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
                }
                
                pair<vector<ui>, vector<ui>> next_C(cur_C);
                int new_tp, new_tn;
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1){
                    new_tp = mav(tp-1, 0);
                    new_tn = tn;
                    next_C.first.push_back(u);
                }
                else{
                    new_tp = tp;
                    new_tn = mav(tn-1, 0);
                    next_C.second.push_back(u);
                }
                mDC(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
                exp_indicator[i-1] = 0;
            }
        }
    }
    else if (tp > 0 && tn == 0){
        vector<ui> tmpvec(vs_size);
        for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
        ui n_idx = 0;
        ui p_idx = n_cand;
        for(ui i = 0; i < vs_size; i++){
            ui u = tmpvec[i];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) vs[p_idx++] = u;
            else vs[n_idx++] = u;
        }
        assert(p_idx == vs_size); assert(n_idx == n_cand);
        
        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        bool pivot_f = true;
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 2) continue;
            if(pivot_indicator[i-1] == 0) continue;
            if(pivot_f){
                for(ui j = 0; j < vs_size; j++){
                    ui v = vs[j];
                    if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                }
                pivot_f = false;
            }
            
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
            }
            
            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            mDC(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
    else if (tp == 0 && tn > 0){
        vector<ui> tmpvec(vs_size);
        for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
        ui n_idx = p_cand;
        ui p_idx = 0;
        for(ui i = 0; i < vs_size; i++){
            ui u = tmpvec[i];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) vs[p_idx++] = u;
            else vs[n_idx++] = u;
        }
        assert(p_idx == p_cand); assert(n_idx == vs_size);

        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        bool pivot_f = true;
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) continue;
            if(pivot_indicator[i-1] == 0) continue;
            if(pivot_f){
                for(ui j = 0; j < vs_size; j++){
                    ui v = vs[j];
                    if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                }
                pivot_f = false;
            }
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
            }

            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            mDC(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
    else{
        assert(tp == 0 && tn == 0);
        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            if(pivot_indicator[i-1] == 0) continue;
            for(ui j = 0; j < vs_size; j++){
                ui v = vs[j];
                if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
            }
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
            }
            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            mDC(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
}

void find_MBC_in_ego_network_BL(pair<vector<ui>, vector<ui>> cur_C, ui * vs, ui vs_size, int tp, int tn)
{
    if(vs_size == 0 && tp == 0 && tn == 0){
        if(psz(cur_C) > psz(cur_MC)) cur_MC = cur_C; return;
    }
    
    if(psz(cur_C) + vs_size <= psz(cur_MC)) return;
    
    obtain_degree(vs, vs_size);
    
    comp_corenum_and_reduce_to_kcore_by_Matrix(vs, vs_size, mav(psz(cur_MC) + 1 - psz(cur_C) - 1, 0));
    if(vs_size == 0) return;
    
    int coUB = color_based_UB_Matrix(vs, vs_size);
    if(coUB < mav(psz(cur_MC) + 1 - psz(cur_C), 0)) return;
    
    int p_cand = 0, n_cand = 0;
    for(ui i = 0; i < vs_size; i++){
        assert(inPN[vs[i]] == 1 || inPN[vs[i]] == 2);
        if(inPN[vs[i]] == 1) ++ p_cand;
        else ++ n_cand;
    }
    if(p_cand < tp || n_cand < tn) return;
    
    if(tp > 0  && tn > 0){
        assert(p_cand > 0); assert(n_cand > 0);
        if(p_cand <= n_cand){ // first select from P
            vector<ui> tmpvec(vs_size);
            for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
            ui n_idx = 0;
            ui p_idx = n_cand;
            for(ui i = 0; i < vs_size; i++){
                ui u = tmpvec[i];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) vs[p_idx++] = u;
                else vs[n_idx++] = u;
            }
            assert(p_idx == vs_size); assert(n_idx == n_cand);

            vector<int> pivot_indicator(vs_size, 1);
            vector<int> exp_indicator(vs_size, 1);
            
            bool pivot_f = true;
            for(ui i = vs_size; i > 0; i--){
                ui u = vs[i-1];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 2) continue;
                if(pivot_indicator[i-1] == 0) continue;
                if(pivot_f){
                    for(ui j = 0; j < vs_size; j++){
                        ui v = vs[j];
                        if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                    }
                    pivot_f = false;
                }
                vector<ui> next_g;
                for(ui j = vs_size; j > 0; j--){
                    ui v = vs[j-1];
                    if(Matrix[trans[u]][trans[v]] == 1 && exp_indicator[j-1] == 1 && inPN[v] == 1) next_g.push_back(v);
                    else if(Matrix[trans[u]][trans[v]] == -1 && exp_indicator[j-1] == 1 && inPN[v] == 2) next_g.push_back(v);
                }
                pair<vector<ui>, vector<ui>> next_C(cur_C);
                int new_tp, new_tn;
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1){
                    new_tp = mav(tp-1, 0);
                    new_tn = tn;
                    next_C.first.push_back(u);
                }
                else{
                    new_tp = tp;
                    new_tn = mav(tn-1, 0);
                    next_C.second.push_back(u);
                }
                find_MBC_in_ego_network_BL(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
                exp_indicator[i-1] = 0;
            }
        }
        else{ // first select from N
            vector<ui> tmpvec(vs_size);
            for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
            ui n_idx = p_cand;
            ui p_idx = 0;
            for(ui i = 0; i < vs_size; i++){
                ui u = tmpvec[i];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) vs[p_idx++] = u;
                else vs[n_idx++] = u;
            }
            assert(p_idx == p_cand); assert(n_idx == vs_size);

            vector<int> pivot_indicator(vs_size, 1);
            vector<int> exp_indicator(vs_size, 1);
            
            bool pivot_f = true;
            for(ui i = vs_size; i > 0; i--){
                ui u = vs[i-1];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) continue;
                if(pivot_indicator[i-1] == 0) continue;
                
                if(pivot_f){
                    for(ui j = 0; j < vs_size; j++){
                        ui v = vs[j];
                        if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                    }
                    pivot_f = false;
                }
                
                vector<ui> next_g;
                for(ui j = vs_size; j > 0; j--){
                    ui v = vs[j-1];
                    if(Matrix[trans[u]][trans[v]] == 1 && exp_indicator[j-1] == 1 && inPN[v] == 2) next_g.push_back(v);
                    else if (Matrix[trans[u]][trans[v]] == -1 && exp_indicator[j-1] == 1 && inPN[v] == 1) next_g.push_back(v);
                }
                
                pair<vector<ui>, vector<ui>> next_C(cur_C);
                int new_tp, new_tn;
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1){
                    new_tp = mav(tp-1, 0);
                    new_tn = tn;
                    next_C.first.push_back(u);
                }
                else{
                    new_tp = tp;
                    new_tn = mav(tn-1, 0);
                    next_C.second.push_back(u);
                }
                find_MBC_in_ego_network_BL(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
                exp_indicator[i-1] = 0;
            }
        }
    }
    else if (tp > 0 && tn == 0){
        vector<ui> tmpvec(vs_size);
        for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
        ui n_idx = 0;
        ui p_idx = n_cand;
        for(ui i = 0; i < vs_size; i++){
            ui u = tmpvec[i];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) vs[p_idx++] = u;
            else vs[n_idx++] = u;
        }
        assert(p_idx == vs_size); assert(n_idx == n_cand);
        
        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        bool pivot_f = true;
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 2) continue;
            if(pivot_indicator[i-1] == 0) continue;
            if(pivot_f){
                for(ui j = 0; j < vs_size; j++){
                    ui v = vs[j];
                    if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                }
                pivot_f = false;
            }
            
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] == 1 && exp_indicator[j-1] == 1 && inPN[v] == 1) next_g.push_back(v);
                else if(Matrix[trans[u]][trans[v]] == -1 && exp_indicator[j-1] == 1 && inPN[v] == 2) next_g.push_back(v);
            }
            
            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            find_MBC_in_ego_network_BL(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
    else if (tp == 0 && tn > 0){
        vector<ui> tmpvec(vs_size);
        for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
        ui n_idx = p_cand;
        ui p_idx = 0;
        for(ui i = 0; i < vs_size; i++){
            ui u = tmpvec[i];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) vs[p_idx++] = u;
            else vs[n_idx++] = u;
        }
        assert(p_idx == p_cand); assert(n_idx == vs_size);

        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        bool pivot_f = true;
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) continue;
            if(pivot_indicator[i-1] == 0) continue;
            if(pivot_f){
                for(ui j = 0; j < vs_size; j++){
                    ui v = vs[j];
                    if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                }
                pivot_f = false;
            }
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] == 1 && exp_indicator[j-1] == 1 && inPN[v] == 2) next_g.push_back(v);
                else if (Matrix[trans[u]][trans[v]] == -1 && exp_indicator[j-1] == 1 && inPN[v] == 1) next_g.push_back(v);
            }

            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            find_MBC_in_ego_network_BL(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
    else{
        assert(tp == 0 && tn == 0);
        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            if(pivot_indicator[i-1] == 0) continue;
            for(ui j = 0; j < vs_size; j++){
                ui v = vs[j];
                if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
            }
            vector<ui> next_g;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                for(ui j = vs_size; j > 0; j--){
                    ui v = vs[j-1];
                    if(Matrix[trans[u]][trans[v]] == 1 && exp_indicator[j-1] == 1 && inPN[v] == 1) next_g.push_back(v);
                    else if (Matrix[trans[u]][trans[v]] == -1 && exp_indicator[j-1] == 1 && inPN[v] == 2) next_g.push_back(v);
                }
            }
            else{
                for(ui j = vs_size; j > 0; j--){
                    ui v = vs[j-1];
                    if(Matrix[trans[u]][trans[v]] == 1 && exp_indicator[j-1] == 1 && inPN[v] == 2) next_g.push_back(v);
                    else if (Matrix[trans[u]][trans[v]] == -1 && exp_indicator[j-1] == 1 && inPN[v] == 1) next_g.push_back(v);
                }
            }
            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            find_MBC_in_ego_network_BL(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
}

void get_its_neighbor(ui u, ui * vs, ui & vs_size)
{
    memset(inPN, 0, sizeof(ui)*n);
    vs_size = 0;
    for(ui i = p_pstart[u]; i < p_pend[u]; i++){
        ui v = p_edges[i];
        vs[vs_size++] = v;
        inPN[v] = 1;
    }
    for(ui i = n_pstart[u]; i < n_pend[u]; i++){
        ui v = n_edges[i];
        vs[vs_size++] = v;
        inPN[v] = 2;
    }
}

void find_MSBC()
{
    Timer t;
    
    //vertex reduction
    ui delv_count = 0;
    bit_del = new ui[n];
    memset(bit_del, 0, sizeof(ui)*n);
    vertex_reduction(delv_count, bit_del);
    shrink_on_reduced_v(bit_del);
    ui now_m = 0, now_pm = 0, now_nm = 0;
    for(ui i = 0; i < n; i++) {now_m += degree[i];now_pm += p_degree[i]; now_nm += n_degree[i];}
    assert(now_m%2 == 0); assert(now_pm%2 == 0); assert(now_nm%2 == 0);
    now_m /= 2; now_pm /= 2; now_nm /= 2;
    cout<<"\t vertex reduce,  T : "<<integer_to_string(t.elapsed())<<"        (n="<<n<<", m="<<now_m<<")."<<endl;
    if(n == 0) return;
    
#ifdef _ER_
    //edge reduction
    t.restart();
    ui dele_count = 0;
    edge_reduction(dele_count);
    shrink_on_reduced_e();
    now_m = 0; now_pm = 0; now_nm = 0;
    for(ui i = 0; i < n; i++) {now_m += degree[i];now_pm += p_degree[i]; now_nm += n_degree[i];}
    assert(now_m%2 == 0); assert(now_pm%2 == 0); assert(now_nm%2 == 0);
    now_m /= 2; now_pm /= 2; now_nm /= 2;
    cout<<"\t edge  reduce ,  T : "<<integer_to_string(t.elapsed())<<"        (n="<<n<<", m="<<now_m<<")."<<endl;
#endif
    
    //find heuristic MSBC
    t.restart();
    heu_MSBC_max_deg_inturn_find_one_stop(10);
    cout<<"\t find heu msbc,  T : "<<integer_to_string(t.elapsed())<<"        (heu_MSBC size = "<<psz(cur_MC)<<" : <"<<cur_MC.first.size()<<","<<cur_MC.second.size()<<">)"<<endl;
    
    //peel, shrink and orient the remaining subgraph
    t.restart();
    degeneracy_order();
    shrink_and_orient_graph();
    ui tmp_m = 0;
    for(ui i = 0; i < n; i++){
        tmp_m += p_pstart_o[i+1] - p_pstart_o[i];
        tmp_m += n_pstart_o[i+1] - n_pstart_o[i];
    }
    cout<<"\t peel orient g,  T : "<<integer_to_string(t.elapsed())<<"        (n="<<n<<", m="<<tmp_m<<")."<<endl;
    
    vector<ui> vsP(d_MAX);
    ui vsP_size;
    vector<ui> vsN(d_MAX);
    ui vsN_size;
    inPN = new ui[n];
    vs_core = new ui[n];
    vs_color = new ui[n];
    Matrix = new int*[max_core];
    for(int i = 0; i < max_core; i++) Matrix[i] = new int[max_core];
    trans = new ui[n];

    CntEgoNet = 0;
    num_of_ori_edges = 0;
    num_of_now_edges = 0;
    num_of_after_reduction_now_edges = 0;

    t.restart();
    for(ui i = n; i > 0; i--){
        
        ui u = i - 1;
        
        if(n - i < psz(cur_MC)) continue;
        
        if(core[u] < psz(cur_MC)) break;

        get_higher_neighbors(u, vsP.data(), vsP_size, vsN.data(), vsN_size);

        if(vsP_size < tau - 1 || vsN_size < tau) continue;
        
        ui tmp_ori_edges, tmp_now_edges;
        
        construct_induced_subgraph(vsP.data(), vsP_size, vsN.data(), vsN_size, tmp_ori_edges, tmp_now_edges);
        
        vs_vertex_reduce(vsP.data(), vsP_size, vsN.data(), vsN_size);
        
        if(vsP_size == 0 && vsN_size == 0) continue;
        
        reduce_to_kcore(vsP.data(), vsP_size, vsN.data(), vsN_size, mav(psz(cur_MC) - 1, tau*2 - 2));
        
        if(vsP_size == 0 && vsN_size == 0) continue;
        
        construct_Matrix(vsP.data(), vsP_size, vsN.data(), vsN_size);

        vector<ui> vs;
        for(ui i = 0; i < vsP_size; i++) vs.push_back(vsP[i]);
        for(ui i = 0; i < vsN_size; i++) vs.push_back(vsN[i]);

        ui tm = 0;
        for(ui i = 0; i < vs.size(); i++) for(ui j = i+1; j< vs.size(); j++)
            if(Matrix[trans[vs[i]]][trans[vs[j]]] == 1 || Matrix[trans[vs[i]]][trans[vs[j]]] == -1) ++ tm;
        
        if(color_based_UB_Matrix(vs.data(), vs.size()) < psz(cur_MC) ) continue;

        pair<vector<ui>, vector<ui>> cur_C;
        cur_C.first.push_back(u);
        
        mDC(cur_C, vs.data(), vs.size(), tau - 1, tau);
        
        ++ CntEgoNet;
        num_of_ori_edges += tmp_ori_edges;
        num_of_now_edges += tmp_now_edges;
        num_of_after_reduction_now_edges += tm;
    }
    cout<<"\t invoking MDC ,  T : "<<integer_to_string(t.elapsed())<<endl;
    cout<<"\t #MDC = "<<CntEgoNet;
    cout<<", SR1 = "<<(1 - (double)num_of_now_edges/num_of_ori_edges) * 100<<"%";
    cout<<", SR2 = "<<(1 - (double)num_of_after_reduction_now_edges/num_of_ori_edges) * 100<<"%."<<endl;
}

void delete_memo()
{
    if(p_pstart != nullptr){
        delete [] p_pstart;
        p_pstart = nullptr;
    }
    if(p_edges != nullptr){
        delete [] p_edges;
        p_edges = nullptr;
    }
    if(p_pend != nullptr){
        delete [] p_pend;
        p_pend = nullptr;
    }
    if(n_pstart != nullptr)
    {
        delete [] n_pstart;
        n_pstart = nullptr;
    }
    if(n_edges != nullptr){
        delete [] n_edges;
        n_edges = nullptr;
    }
    if(n_pend != nullptr){
        delete [] n_pend;
        n_pend = nullptr;
    }
    
    if(p_pstart_o != nullptr){
        delete [] p_pstart_o;
        p_pstart_o = nullptr;
    }
    if(p_edges_o != nullptr){
        delete [] p_edges_o;
        p_edges_o = nullptr;
    }
    if(n_pstart_o != nullptr){
        delete [] n_pstart_o;
        n_pstart_o = nullptr;
    }
    if(n_edges_o != nullptr){
        delete [] n_edges_o;
        n_edges_o = nullptr;
    }
    
    if(p_pstart != nullptr){
        delete [] degree;
        degree = nullptr;
    }
    if(p_pstart != nullptr){
        delete [] p_degree;
        p_degree = nullptr;
    }
    if(p_pstart != nullptr){
        delete [] n_degree;
        n_degree = nullptr;
    }
    
    if(sup_pp != nullptr){
        delete [] sup_pp;
        sup_pp = nullptr;
    }
    if(sup_nn != nullptr){
        delete [] sup_nn;
        sup_nn = nullptr;
    }
    if(sup_np != nullptr){
        delete [] sup_np;
        sup_np = nullptr;
    }
    if(e_sign != nullptr){
        delete [] e_sign;
        e_sign = nullptr;
    }
    if(e_del != nullptr){
        delete [] e_del;
        e_del = nullptr;
    }
    if(core != nullptr){
        delete [] core;
        core = nullptr;
    }
    if(peel_s != nullptr){
        delete [] peel_s;
        peel_s = nullptr;
    }
    if(inPN != nullptr){
        delete [] inPN;
        inPN = nullptr;
    }
    if(vs_core != nullptr){
        delete [] vs_core;
        vs_core = nullptr;
    }
    if(vs_color != nullptr){
        delete [] vs_color;
        vs_color = nullptr;
    }
    for(int i = 0; i < max_core; i++) if(Matrix[i] != nullptr){
        delete [] Matrix[i];
        Matrix[i] = nullptr;
    }
    if(trans != nullptr){
        delete [] trans;
        trans = nullptr;
    }
    if(bit_del != nullptr){
        delete [] bit_del;
        bit_del = nullptr;
    }
    if(PNdeg != nullptr){
        delete [] PNdeg;
        PNdeg = nullptr;
    }
    if(ori_id != nullptr){
        delete [] ori_id;
        ori_id = nullptr;
    }
}

//greegy search until find one solution, at most 'rounds' tries.
void heu_Mtau_find_one_stop(ui rounds)
{
    Mtau = 1;
    if(rounds < 1) return;
    priority_queue<pair<ui, ui>, vector<pair<ui, ui>>, greater<pair<ui, ui>>> kset;
    for (ui i = 0; i < rounds; i++) {
        kset.push(make_pair(miv(p_degree[i], n_degree[i]), i));
    }
    for(ui i = rounds; i < n; i++){
        ui itsdeg = miv(p_degree[i], n_degree[i]);
        if(itsdeg > kset.top().first){
            kset.pop();
            kset.push(make_pair(itsdeg, i));
        }
    }
    vector<pair<ui, ui>> ordV(rounds);
    for(ui i = 0; i < rounds; i++){
        ordV[i] = kset.top();
        kset.pop();
    }
    
    sort(ordV.begin(), ordV.end(), greater<>());
    
    ui * label = new ui[n];
    ui * vs_deg = new ui[n];
    for(ui round = 0; round < rounds && round < n; round++){
        ui u = ordV[round].second;
        memset(label, 0, sizeof(ui)*n);
        pair<vector<ui>, vector<ui>> res;
        res.first.push_back(u);
        vector<ui> vsP, vsN;
        for(ui i = p_pstart[u]; i < p_pend[u]; i++){
            ui v = p_edges[i];
            vsP.push_back(v);
            label[v] = 1;
        }
        for(ui i = n_pstart[u]; i < n_pend[u]; i++){
            ui v = n_edges[i];
            vsN.push_back(v);
            label[v] = 2;
        }
        for(auto e : vsP) vs_deg[e] = 0;
        for(auto e : vsN) vs_deg[e] = 0;
        for(auto e : vsP){
            for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                ui v = p_edges[i];
                if(label[v] == 1) ++ vs_deg[e];
            }
            for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                ui v = n_edges[i];
                if(label[v] == 2) ++ vs_deg[e];
            }
        }
        for(auto e : vsN){
            for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                ui v = p_edges[i];
                if(label[v] == 2) ++ vs_deg[e];
            }
            for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                ui v = n_edges[i];
                if(label[v] == 1) ++ vs_deg[e];
            }
        }

        while (!vsP.empty() || !vsN.empty()) {
            if(res.first.size() >= res.second.size()){ // next vertex will select from vsN
                if(vsN.empty()) break;
                ui tmp_deg = 0;
                ui next_v;
                for(ui i = 0; i < vsN.size(); i++){
                    if(vs_deg[vsN[i]] >= tmp_deg){
                        tmp_deg = vs_deg[vsN[i]];
                        next_v = vsN[i];
                    }
                }
                res.second.push_back(next_v);
                vector<ui> new_vsP, new_vsN;
                assert(label[next_v] == 2);
                for(ui i = p_pstart[next_v]; i < p_pend[next_v]; i++){
                    ui v = p_edges[i];
                    if(label[v] == 2) new_vsN.push_back(v);
                }
                for(ui i = n_pstart[next_v]; i < n_pend[next_v]; i++){
                    ui v = n_edges[i];
                    if(label[v] == 1) new_vsP.push_back(v);
                }
                for(auto e : vsP) label[e] = 0;
                for(auto e : vsN) label[e] = 0;
                vsP = new_vsP;
                vsN = new_vsN;
                for(auto e : vsP) label[e] = 1;
                for(auto e : vsN) label[e] = 2;
                for(auto e : vsP) vs_deg[e] = 0;
                for(auto e : vsN) vs_deg[e] = 0;
                for(auto e : vsP){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                }
                for(auto e : vsN){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                }
            }
            else{ // next vertex will select from vsP
                if(vsP.empty()) break;
                ui tmp_deg = 0;
                ui next_v;
                for(ui i = 0; i < vsP.size(); i++){
                    if(vs_deg[vsP[i]] >= tmp_deg){
                        tmp_deg = vs_deg[vsP[i]];
                        next_v = vsP[i];
                    }
                }
                res.first.push_back(next_v);
                vector<ui> new_vsP, new_vsN;
                assert(label[next_v] == 1);
                for(ui i = p_pstart[next_v]; i < p_pend[next_v]; i++){
                    ui v = p_edges[i];
                    if(label[v] == 1) new_vsP.push_back(v);
                }
                for(ui i = n_pstart[next_v]; i < n_pend[next_v]; i++){
                    ui v = n_edges[i];
                    if(label[v] == 2) new_vsN.push_back(v);
                }
                for(auto e : vsP) label[e] = 0;
                for(auto e : vsN) label[e] = 0;
                vsP = new_vsP;
                vsN = new_vsN;
                for(auto e : vsP) label[e] = 1;
                for(auto e : vsN) label[e] = 2;
                for(auto e : vsP) vs_deg[e] = 0;
                for(auto e : vsN) vs_deg[e] = 0;
                for(auto e : vsP){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                }
                for(auto e : vsN){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                }
            }
        }
        if(miv(res.first.size(), res.second.size()) > Mtau){
            Mtau = miv(res.first.size(), res.second.size());
            break;
        }
    }
    delete [] label;
    delete [] vs_deg;
}

void inrecur_vs_vertex_reduce_Mtau_by_Matrix(ui * vs, ui & vs_size, int tp, int tn)
{
    int vsP_pt = mav(tp - 1, 0);
    int vsP_nt = tn;
    
    int vsN_pt = mav(tn - 1, 0);
    int vsN_nt = tp;
    
    for(ui i = 0; i < vs_size; i++) bit_del[vs[i]] = 0;

    queue<ui> Q;
    for(ui i = 0; i < vs_size; i++){
        ui u = vs[i];
        assert(inPN[u] == 1 || inPN[u] == 2);
        if(inPN[u] == 1){
            if(p_degree[u] < vsP_pt || n_degree[u] < vsP_nt) {
                Q.push(u);
            }
        }
        else{
            if(p_degree[u] < vsN_pt || n_degree[u] < vsN_nt) {
                Q.push(u);
            }
        }
    }
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        
        p_degree[u] = 0;
        n_degree[u] = 0;
        bit_del[u] = 1;
        
        assert(inPN[u] == 1 || inPN[u] == 2);
        if(inPN[u] == 1){
            for(ui i = 0; i < vs_size; i++){
                ui v = vs[i];
                if(Matrix[trans[u]][trans[v]] == 1){
                    assert(inPN[v] == 1);
                    if(p_degree[v] > 0){
                        if((p_degree[v]--) == vsP_pt && n_degree[v] >= vsP_nt){
                            Q.push(v);
                        }
                    }
                }
                else if(Matrix[trans[u]][trans[v]] == -1){
                    assert(inPN[v] == 2);
                    if(n_degree[v] > 0){
                        if((n_degree[v]--) == vsN_nt && p_degree[v] >= vsN_pt){
                            Q.push(v);
                        }
                    }
                }
            }
        }
        else{
            for(ui i = 0; i < vs_size; i++){
                ui v = vs[i];
                if(Matrix[trans[u]][trans[v]] == 1){
                    assert(inPN[v] == 2);
                    if(p_degree[v] > 0){
                        if((p_degree[v]--) == vsN_pt && n_degree[v] >= vsN_nt){
                            Q.push(v);
                        }
                    }
                }
                else if(Matrix[trans[u]][trans[v]] == -1){
                    assert(inPN[v] == 1);
                    if(n_degree[v] > 0){
                        if((n_degree[v]--) == vsP_nt && p_degree[v] >= vsP_pt){
                            Q.push(v);
                        }
                    }
                }
            }
        }
    }
    
    for(ui i = 0; i < vs_size; i++) degree[vs[i]] = p_degree[vs[i]] + n_degree[vs[i]];
    
#ifdef _DEBUG_
    cout<<"each vertex degree after inrecur_vs_vertex_reduce_Mtau_by_Matrix(): "<<endl;
    for(ui i = 0; i < vs_size; i++){
        cout<<"vertex "<<vs[i]<<": degree = "<<degree[vs[i]]<<", p_degree = "<<p_degree[vs[i]]<<", n_degree = "<<n_degree[vs[i]]<<endl;
    }
    cout<<endl;
#endif
    ui vs_new_size = 0;
    for(ui i = 0; i < vs_size; i++){
        ui u = vs[i];
        if(bit_del[u] == 0)
            vs[vs_new_size++] = u;
    }
    vs_size = vs_new_size;
#ifdef _DEBUG_
    cout<<"remaining vertices: "<<endl;
    for(ui i = 0; i < vs_size; i++) cout<<vs[i]<<", "; cout<<endl;
#endif
}

pair<vector<ui>, vector<ui>> kDC(ui * vs, ui vs_size, int tp, int tn)
{
    assert(tp >= 0 && tn >= 0);
    pair<vector<ui>, vector<ui>> empty_set;
    if(tp == 0 && tn == 0) return empty_set;
    if(vs_size < tp + tn) return empty_set;
    
    int p_cand = 0, n_cand = 0;
    for(ui i = 0; i < vs_size; i++){
        assert(inPN[vs[i]] == 1 || inPN[vs[i]] == 2);
        if(inPN[vs[i]] == 1) ++ p_cand;
        else ++ n_cand;
    }
    if(p_cand < tp || n_cand < tn) return empty_set;
    
    obtain_degree_Mtau(vs, vs_size);
    inrecur_vs_vertex_reduce_Mtau_by_Matrix(vs, vs_size, tp, tn);
    if(vs_size == 0) return empty_set;
    
    p_cand = 0; n_cand = 0;
    for(ui i = 0; i < vs_size; i++){
        assert(inPN[vs[i]] == 1 || inPN[vs[i]] == 2);
        if(inPN[vs[i]] == 1) ++ p_cand;
        else ++ n_cand;
    }
    if(p_cand < tp || n_cand < tn) return empty_set;
    
    
    if(tp >= tn){ //only choose vertex in vsP
        //reorder vs
        vector<ui> tmpvec(vs_size);
        for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
        ui n_idx = 0;
        ui p_idx = n_cand;
        for(ui i = 0; i < vs_size; i++){
            ui u = tmpvec[i];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) vs[p_idx++] = u;
            else vs[n_idx++] = u;
        }
        assert(p_idx == vs_size); assert(n_idx == n_cand);
        
        vector<int> pivot_indicator(vs_size, 1);
        bool pivot_f = true;
        vector<int> exp_indicator(vs_size, 1);
        
        for(ui i = vs_size; i > 0; i--){
            
            ui u = vs[i-1];
            assert(inPN[u] == 1 || inPN[u] == 2);
            
            if(inPN[u] == 2) continue;
            if(pivot_indicator[i-1] == 0) continue;
            
            if(pivot_f){
                for(ui j = 0; j < vs_size; j++){
                    ui v = vs[j];
                    if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                }
                pivot_f = false;
            }
            
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1){
                    next_g.push_back(v);
                }
            }
                        
            assert(inPN[u] == 1);
            pair<vector<ui>, vector<ui>> tmp_res;
            assert(tp >= 1);
            int new_tp = tp - 1;
            int new_tn = tn;
            tmp_res = kDC(next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
            if(tmp_res.first.size() == new_tp && tmp_res.second.size() == new_tn){
                tmp_res.first.push_back(u);
                return tmp_res;
            }
        }
        return empty_set;
    }
    else{ //tp < tn, only choose vertex in vsN
        //reorder vs
        vector<ui> tmpvec(vs_size);
        for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
        ui n_idx = p_cand;
        ui p_idx = 0;
        for(ui i = 0; i < vs_size; i++){
            ui u = tmpvec[i];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) vs[p_idx++] = u;
            else vs[n_idx++] = u;
        }
        assert(p_idx == p_cand); assert(n_idx == vs_size);
        
        vector<int> pivot_indicator(vs_size, 1);
        bool pivot_f = true;
        vector<int> exp_indicator(vs_size, 1);
        
        for(ui i = vs_size; i > 0; i--){
            
            ui u = vs[i-1];
            assert(inPN[u] == 1 || inPN[u] == 2);
            
            if(inPN[u] == 1) continue;
            if(pivot_indicator[i-1] == 0) continue;
            
            if(pivot_f){
                for(ui j = 0; j < vs_size; j++){
                    ui v = vs[j];
                    if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                }
                pivot_f = false;
            }
            
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1){
                    next_g.push_back(v);
                }
            }
                        
            assert(inPN[u] == 2);
            pair<vector<ui>, vector<ui>> tmp_res;
            assert(tn >= 1);
            int new_tp = tp;
            int new_tn = tn - 1;
            tmp_res = kDC(next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
            if(tmp_res.first.size() == new_tp && tmp_res.second.size() == new_tn){
                tmp_res.second.push_back(u);
                return tmp_res;
            }
        }
        return empty_set;
    }
}

void get_higher_neighbors_Mtau(ui u, ui * vsP, ui &vsP_size, ui * vsN, ui &vsN_size)
{
    for(ui i = 0; i < n; i++) inPN[i] = 0;
    vsP_size = 0;
    for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
        vsP[vsP_size++] = p_edges_o[j];
        inPN[p_edges_o[j]] = 1;
    }
    vsN_size = 0;
    for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
        vsN[vsN_size++] = n_edges_o[j];
        inPN[n_edges_o[j]] = 2;
    }
}

void find_Mtau()
{
    Timer t;

    //find heuristic tau
    heu_Mtau_find_one_stop(10);
    cout<<"\t heuristicMtau,  T : "<<integer_to_string(t.elapsed())<<"        (heu_Mtau = "<<Mtau<<")."<<endl;
    
    //vertex reduction
    t.restart();
    ui now_m, now_pm, now_nm;
    ui delv_count = 0;
    bit_del = new ui[n];
    memset(bit_del, 0, sizeof(ui)*n);
    tau = Mtau;
    vertex_reduction(delv_count, bit_del);
    shrink_on_reduced_v(bit_del);
    now_m = 0; now_pm = 0; now_nm = 0;
    for(ui i = 0; i < n; i++) {now_m += degree[i];now_pm += p_degree[i]; now_nm += n_degree[i];}
    assert(now_m%2 == 0); assert(now_pm%2 == 0); assert(now_nm%2 == 0);
    now_m /= 2; now_pm /= 2; now_nm /= 2;
    cout<<"\t vertex reduce,  T : "<<integer_to_string(t.elapsed())<<"        (n="<<n<<", m="<<now_m<<")."<<endl;
    if(n == 0) return;
        
#ifdef _MtauPNORDER_
    t.restart();
    PN_order();
    cout<<"\t obtain POrder,  T : "<<integer_to_string(t.elapsed())<<endl;
    t.restart();
    shrink_and_orient_graph_Mtau_PNorder();
    ui tmp_m = 0;
    for(ui i = 0; i < n; i++){
        tmp_m += p_pstart_o[i+1] - p_pstart_o[i];
        tmp_m += n_pstart_o[i+1] - n_pstart_o[i];
    }
    cout<<"\t shrink_orient,  T : "<<integer_to_string(t.elapsed())<<"        (n="<<n<<", m="<<tmp_m<<")."<<endl;
#else
    t.restart();
    degeneracy_order();
    cout<<"\t obtain DOrder,  T : "<<integer_to_string(t.elapsed())<<endl;
    t.restart();
    shrink_and_orient_graph_Mtau_dorder();
    ui tmp_m = 0;
    for(ui i = 0; i < n; i++){
        tmp_m += p_pstart_o[i+1] - p_pstart_o[i];
        tmp_m += n_pstart_o[i+1] - n_pstart_o[i];
    }
    cout<<"\t shrink_orient,  T : "<<integer_to_string(t.elapsed())<<"        (n="<<n<<", m="<<tmp_m<<")."<<endl;
#endif
    
    vector<ui> vsP(d_MAX);
    ui vsP_size;
    vector<ui> vsN(d_MAX);
    ui vsN_size;
    vs_core = new ui[n];
    vs_color = new ui[n];
    inPN = new ui[n];
    Matrix = new int*[d_MAX];
    for(int i = 0; i < d_MAX; i++) Matrix[i] = new int[d_MAX];
    trans = new ui[n];
    
    CntEgoNet = 0;
    num_of_ori_edges = 0;
    num_of_now_edges = 0;
    num_of_after_reduction_now_edges = 0;
    
    t.restart();
    for(ui i = n; i > 0; i--){
        
        ui u = i - 1;
        
        if(n - i < 2 * Mtau + 1) continue;
        
        if(core[u] < Mtau + 1) break;
        
        get_higher_neighbors_Mtau(u, vsP.data(), vsP_size, vsN.data(), vsN_size);

        if(vsP_size < Mtau || vsN_size <= Mtau) continue;
        
        ui tmp_ori_edges = 0, tmp_now_edges = 0;
        
        construct_induced_subgraph(vsP.data(), vsP_size, vsN.data(), vsN_size, tmp_ori_edges, tmp_now_edges);

        vs_vertex_reduce_Mtau(vsP.data(), vsP_size, vsN.data(), vsN_size);
        
        if(vsP_size == 0 && vsN_size == 0) continue;
                
        construct_Matrix(vsP.data(), vsP_size, vsN.data(), vsN_size);

        vector<ui> vs;
        for(ui i = 0; i < vsP_size; i++) vs.push_back(vsP[i]);
        for(ui i = 0; i < vsN_size; i++) vs.push_back(vsN[i]);

        ui tm = 0;
        for(ui i = 0; i < vs.size(); i++) for(ui j = i+1; j< vs.size(); j++)
            if(Matrix[trans[vs[i]]][trans[vs[j]]] == 1 || Matrix[trans[vs[i]]][trans[vs[j]]] == -1) ++ tm;
        
        pair<vector<ui>, vector<ui>> tmp_C;
        int tp = Mtau;
        int tn = Mtau + 1;
        tmp_C = kDC(vs.data(), vs.size(), tp, tn);
        if(tmp_C.first.size() == tp && tmp_C.second.size() == tn) ++ Mtau;
        
        ++ CntEgoNet;
        num_of_ori_edges += tmp_ori_edges;
        num_of_now_edges += tmp_now_edges;
        num_of_after_reduction_now_edges += tm;
    }
    cout<<"\t invoking DCC ,  T : "<<integer_to_string(t.elapsed())<<endl;
    cout<<"\t #DCC = "<<CntEgoNet;
    cout<<", SR1 = "<<(1 - (double)num_of_now_edges/num_of_ori_edges) * 100<<"%";
    cout<<", SR2 = "<<(1 - (double)num_of_after_reduction_now_edges/num_of_ori_edges) * 100<<"%."<<endl;
}

void find_Mtau_binary()
{
    int tau_star = 0;
    
    ui original_n = n;
    ui original_m = m;
    ui original_pm = pm;
    ui original_nm = nm;
    ui original_d_MAX = d_MAX;
    
    ui * original_p_pstart = new ui[n+1];
    ui * original_p_edges = new ui[2*pm];
    ui * original_p_pend = new ui[n];
    ui * original_n_pstart = new ui[n+1];
    ui * original_n_edges = new ui[2*nm];
    ui * original_n_pend = new ui[n];
    
    ui * original_degree = new ui[n];
    ui * original_p_degree = new ui[n];
    ui * original_n_degree = new ui[n];
    
    for(ui i = 0; i < n+1; i++) original_p_pstart[i] = p_pstart[i];
    for(ui i = 0; i < 2*pm; i++) original_p_edges[i] = p_edges[i];
    for(ui i = 0; i < n; i++) original_p_pend[i] = p_pend[i];
    
    for(ui i = 0; i < n+1; i++) original_n_pstart[i] = n_pstart[i];
    for(ui i = 0; i < 2*nm; i++) original_n_edges[i] = n_edges[i];
    for(ui i = 0; i < n; i++) original_n_pend[i] = n_pend[i];
    
    for(ui i = 0; i < n; i++){
        original_degree[i] = degree[i];
        original_p_degree[i] = p_degree[i];
        original_n_degree[i] = n_degree[i];
    }
    int round = 0;
    int L = 1;
    int U = d_MAX;
    while (L <= U) {
        
        n = original_n;
        m = original_m;
        pm = original_pm;
        nm = original_nm;
        d_MAX = original_d_MAX;
        
        p_pstart = new ui[n+1];
        p_edges = new ui[2*pm];
        p_pend = new ui[n];
        n_pstart = new ui[n+1];
        n_edges = new ui[2*nm];
        n_pend = new ui[n];
        
        degree = new ui[n];
        p_degree = new ui[n];
        n_degree = new ui[n];
        
        for(ui i = 0; i < n+1; i++)  p_pstart[i] = original_p_pstart[i];
        for(ui i = 0; i < 2*pm; i++)  p_edges[i] = original_p_edges[i];
        for(ui i = 0; i < n; i++)  p_pend[i] = original_p_pend[i];
        
        for(ui i = 0; i < n+1; i++)  n_pstart[i] = original_n_pstart[i];
        for(ui i = 0; i < 2*nm; i++)  n_edges[i] = original_n_edges[i];
        for(ui i = 0; i < n; i++)  n_pend[i] = original_n_pend[i];
        
        for(ui i = 0; i < n; i++){
             degree[i] = original_degree[i];
             p_degree[i] = original_p_degree[i];
             n_degree[i] = original_n_degree[i];
        }
        
        cur_MC.first.clear(); cur_MC.first.shrink_to_fit();
        cur_MC.second.clear(); cur_MC.second.shrink_to_fit();
        assert(psz(cur_MC) == 0);
        int mid = (L + U) / 2;
        tau = mid;
        Timer ttt;
        cout<<endl<<"\t round "<<++ round<<", L = "<<L<<", U = "<<U<<", tau = "<<mid<<endl;
        
        find_MSBC();
        
        delete_memo();
        
        if(psz(cur_MC) != 0){
            tau_star = mid;
            L = mid + 1;
        }
        else{
            U = mid - 1;
        }
    }
    delete [] original_p_pstart;
    delete [] original_p_edges;
    delete [] original_p_pend;
    delete [] original_n_pstart;
    delete [] original_n_edges;
    delete [] original_n_pend;
    
    delete [] original_degree;
    delete [] original_p_degree;
    delete [] original_n_degree;
    
    Mtau = tau_star;
}

int main(int argc, const char * argv[]) {
    
    if(argc < 3) {
        cout<<"\t Usage: [0]exe [1]input_graph [2]MSBC/Mtau/Mtau_bi [3]tau (optional) \t"<<endl; exit(1);
    }
    
    load_graph(argv[1]);
    string algo = argv[2];
    tau = 3;
    if(argc > 3) tau = atoi(argv[3]);
    
#ifdef _ER_
    cout<<"\t *** _ER_";
#else
    cout<<"\t *** NO _ER_";
#endif
    
#ifdef _COLORUB_
    cout<<", _COLORUB_";
#else
    cout<<", NO _COLORUB_";
#endif
    
#ifdef _MtauPNORDER_
    cout<<", _Porder_";
#else
    cout<<", _Dorder_";
#endif
    
#ifdef _CaseStudy_
    cout<<", _CaseStudy_"<<" ***"<<endl;
#else
    cout<<", NO _CaseStudy_"<<" ***"<<endl;
#endif
    
    cout<<"\t Graph: "<<argv[1]<<", Algo: "<<algo<<endl;
    
    Timer t;
    
    if(algo.compare("MSBC") == 0){
        
        cout<<"\t tau: "<<tau<<endl;
        
        find_MSBC();  //detecting the maximum balanced clique
        
    }
    else if (algo.compare("Mtau_bi") == 0){
        
        find_Mtau_binary();  //detecting the polarization factor in binary way
        
    }
    else if (algo.compare("Mtau") == 0){
        
        find_Mtau();  //detecting the polarization factor
        
    }
    else{
        
        cout<<"\t no matching algorithm!"<<endl; exit(1);
        
    }
    
    cout<<"\t -------------------------------"<<endl;
    if(algo.compare("MSBC") == 0) cout<<"\t final MSBC size = "<<psz(cur_MC)<<" : <"<<cur_MC.first.size()<<","<<cur_MC.second.size()<<">"<<endl;
    else cout<<"\t Mtau = "<<Mtau<<endl;
    cout<<"\t time cost  = "<<integer_to_string(t.elapsed())<<endl;
    cout<<"\t -------------------------------"<<endl;
    
    delete_memo();
    
    return 0;
}

