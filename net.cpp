//
//  Created by 李楚鸣 on 2016/12/5.
//  Copyright © 2016年 李楚鸣. All rights reserved.
//
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <stdio.h>
#include <string.h>
#include "stdlib.h"
#include "time.h"
#include <map>
#include <vector>
#include <cmath>
#include <algorithm>
#include <queue>
#include <functional>
#include <set>
#include <boost/python.hpp>
//port number is 4 or 8

#define port_num 4 //port number
#define ToRnum (port_num * port_num / 2)//4*4/2=8
#define Aggnum (port_num * port_num / 2)//4*4/2=8
#define corenum (port_num * port_num / 4)//4*4/4=4
#define maxn (ToRnum + Aggnum + corenum)//8+8+4=20
#define maxm ToRnum//8
#define k   4//(port_num * 3 - 8) //k shortest path

#define inf 100000000
#define INCREMENT 1.1e7  //150MB/s 1.5e8  15MB/s 1.5e7
#define TTTHRESH INCREMENT*16
//#define Task 100
#define CAPACITY 1.25e9   //1.25GByte/s
#define SCALE 1
#define RTT 1				//100us
#define SSTHRESH 32*INCREMENT //暂时没用
#define CONGESTIONFLAG 0.75  //暂时没用
//input demand 100~1e10 B
//using namespace std;
struct A {
    int id;
    int g, f;
    bool operator <(const A a) const {
        if (a.f == f) return a.g<g;//设置优先级，小的先出
        return a.f<f;
    }
};//A*算法所需要的数据结构
using namespace boost::python;
struct net{
    std::vector<int> stp;
    std::vector<int> stv;
    std::vector<int> e[maxn];
    double f[maxm][maxm];
    std::map<int, int> ehash;//给边标号
    int aNum = 0, eNum = 0, fNum = 0,tNum=0, dist[maxn], Next[maxn];//eNum表示边数，fNum表示流的个数，dist和Next存储最短路算法的结果（每个节点到目标节点的举例和每个节点在到目标点的最短路径上的下一跳）
    std::vector< std::set<int> > e2f;//每个边对应哪些流
    std::map<int, double> fV;//每个流对应的当前速度
    std::map<int, double> fT;//每个流对应的当前阈值
    std::map<int, std::pair<int,int> > f2t;//每个流对应什么任务
    std::vector<int> t2f[maxm][maxm];//每个任务对应哪些流
    
    void clearAll() {
        srand((unsigned)time(NULL));//初始化随机数种子
        for (int i = 0; i<maxn; i++)e[i].clear();
        eNum = fNum = 0;
        e2f.clear();
        ehash.clear();
        fV.clear();
        fT.clear();
        f2t.clear();
        for(int i=0;i<maxm;i++){
            for(int j=0;j<maxm;j++){
                t2f[i][j].clear();
            }
        }
    }
    void hashEdge(){
        for (int i = 0; i<maxn; i++) {
            for (int j = 0; j<e[i].size(); j++) {
                if (j>i) {
                    ehash[maxn*i + j] = eNum++;
                }
            }
        }//prlong longf("eNum: %d\n",eNum);
        for (int i = 0; i<eNum; i++) {
            std::set<int> st;
            e2f.push_back(st);
        }
    }//将边映射到标号
    void readEdge(std::string s) {
        std::ifstream in(s.c_str());
        int a;
        for (int i = 0; i<maxn; i++) {
            for (int j = 0; j<maxn; j++) {
                in >> a;
                if (a == 1) {
                    e[i].push_back(j);
                }
            }
        }
        hashEdge();
        in.close();
    }
    void readEdgeFromPython(boost::python::list l) {
        int f;
        for (int i = 0; i<maxn; i++) {
            boost::python::list ll = call_method<boost::python::list>(l.ptr(),"__getitem__",i);
            for (int j = 0; j<maxn; j++) {
                f  = call_method<int>(ll.ptr(),"__getitem__",j);
                if (f) {
                    e[i].push_back(j);
                }
            }
        }
        hashEdge();
    }
    void addFlow(int p,int x,int y) {
        int eid, a, b;
        while (stp[p] != -1) {
            //prlong longf("%d<-",stv[p]);
            a = std::min(stv[p], stv[stp[p]]);
            b = std::max(stv[p], stv[stp[p]]);//cout<<stv[p]<<" "<<stv[stp[p]]<<" ";
            eid = ehash[maxn*a + b];
            e2f[eid].insert(fNum);
            p = stp[p];
        }//prlong longf("0\n");
        //cout<<endl;
        fV[fNum] = (double)INCREMENT;
        fT[fNum] = (double)TTTHRESH;
        f2t[fNum++] = std::pair<int,int>(x,y);
        t2f[x][y].push_back(fNum);
    }
    
    void addTask(int s, int t) {
        //prlong longf("find dist\n");
        stp.clear();
        stv.clear();
        aNum=0;
        for (int i = 0; i<maxn; i++)dist[i] = inf;
        dist[t] = 0;
        std::priority_queue< std::pair<int,int>, std::vector< std::pair<int, int> >, std::greater< std::pair<int,int> > >que;
        que.push(std::pair<int, int>(0, t));
        while (!que.empty()) {
            std::pair<int, int> p = que.top();
            que.pop();
            int v = p.second;
            if (dist[p.second]<p.first)continue;
            for (int i = 0; i<e[v].size(); i++) {
                if (dist[e[v][i]]>dist[v] + 1) {
                    dist[e[v][i]] = dist[v] + 1;
                    Next[e[v][i]] = v;
                    std::pair<int, int> pp = std::pair<int,int>(dist[e[v][i]], e[v][i]);
                    que.push(pp);
                }
            }
        }//堆优化的迪杰斯特拉
        //************** "A*"算法
        //prlong longf("find path\n");
        std::priority_queue<A>qA;
        A c,ne;
        stp.push_back(-1);
        stv.push_back(s);
        c.id = aNum++;
        c.g = 0;
        c.f = dist[s];
        qA.push(c);
        int kk = k;
        while (!qA.empty()) {
            c = qA.top(); qA.pop();
            if ((stv[c.id]) == t) {//prlong longf("add a new flow\n");
                addFlow(c.id,s,t);
                kk--;
                if (kk == 0)break;
            }
            else{
                for (int i = 0; i<e[stv[c.id]].size(); i++) {
                    int v = e[stv[c.id]][i], f = 1;
                    int p = c.id;
                    while (p != -1) {
                        if (stv[p] == v) {
                            f = 0;
                            break;
                        }
                        p = stp[p];
                    }
                    if (f) {
                        stp.push_back(c.id);
                        stv.push_back(v);
                        ne.id = aNum++;
                        ne.g = c.g + 1;
                        ne.f = ne.g + dist[v];
                        qA.push(ne);
                    }//由于是无向图跑A*算法，需要存一个链表记录队列中的每个节点经过的路径,每次一个节点入队列都要保证该节点经过的路径上无环
                }
            }
        }
        //*********************
    }
    void readTask(std::string s) {
        std::ifstream in(s.c_str());
        double temp_in = 0;
        for (int i = 0; i<maxm; i++) {
            for (int j = 0; j<maxm; j++) {
                in >> temp_in;
                f[i][j]=temp_in*SCALE;
                //			cout << "i:" << i << " j:" << j << endl;
                //			cout << f[i][j] << endl;
            }
        }
        for (int i = 0; i<maxm; i++) {
            for (int j = i + 1; j<maxm; j++) {
                f[i][j]=f[i][j] + f[j][i];
                f[j][i]=0;
            }
        }
        in.close();
    }
    void readTaskFromPython(boost::python::list l){
        for(int i=0;i<maxm;i++){
            boost::python::list ll = call_method<boost::python::list>(l.ptr(),"__getitem__",i);
            for(int j=0;j<maxm;j++){
                f[i][j]=(double)call_method<int>(ll.ptr(),"__getitem__",j);
            }
        }
        for (int i = 0; i<maxm; i++) {
            for (int j = i + 1; j<maxm; j++) {
                f[i][j]=f[i][j] + f[j][i];
            }
        }
    }
    void setTask(){
        for (int i = 0; i<maxm; i++) {
            for (int j = i + 1; j<maxm; j++) {
                if(f[i][j]>0){
                    addTask(i, j);
                }
            }
        }
    }
    boost::python::list getTaskFromCpp(){
        boost::python::list l;
        for (int i = 0; i<maxm; i++) {
            boost::python::list ll;
            for (int j = 0; j<maxm; j++) {
                ll.append(f[i][j]);
            }l.append(ll);
        }return l;
    }
    int RunATcik(){
        std::map<int,double>::iterator fit;
        std::set<int> block;//存储哪些流被减速了
        for(fit=fV.begin();fit!=fV.end();fit++){
            if(fit->second<fT[fit->first])fit->second*=2;
            else fit->second+=(double)INCREMENT;
        }//先对所有的流进行增大处理
        for (int i = 0; i<eNum; i++) {
            int num = 0;//该边经过的总流个数
            double eC = 0;//该边总流速
            std::vector<int> del;//该边上需要删除的流
            std::set<int> tp;//暂存所有可能被减半的流
            std::set<int>::iterator it;
            for (it = e2f[i].begin(); it != e2f[i].end(); it++) {//*********** 对每条边监测边上还有哪些未完成的流
                if (fV.find(*it) != fV.end()) {//确保是未完成的流
                    eC += fV[*it];
                    tp.insert(*it);
                    num++;
                }
                else del.push_back(*it);
            }
            for (int j = 0; j<del.size(); j++)e2f[i].erase(del[j]);//删除该链路上已经完成的流
            if (eC>CAPACITY)//边不满 对每个流进行增大
            {
                while(eC>CAPACITY){//cout<<eC;
                    int id=rand()%num+1;
                    for (it = tp.begin(); it != tp.end(); it++) {
                        id--;
                        if(id==0){
                            fV[*it]/=2;
                            eC-=fV[*it];
                            //tp.erase(*it);
                            //num--;    //这两句加上就能保证每次不减半同一个流的速度
                            break;
                        }
                    }
                }
            }
        }
        std::map<int, double>::iterator it2;
        for (it2 = fV.begin(); it2 != fV.end(); it2++) {
            f[f2t[it2->first].first][f2t[it2->first].second] -= it2->second*RTT;
        }
        int at=0;//存储所有alive的task的个数
        for(int i=0;i<maxm;i++){
            for (int j=i+1; j<maxm; j++) {
                if (f[i][j] <=0) {
                    f[i][j]=0;
                    if(t2f[i][j].size()>0){
                        std::vector<int> ff = t2f[i][j];
                        for (int t = 0; t<ff.size(); t++) {
                            f2t.erase(ff[t]);
                            fV.erase(ff[t]);
                            fT.erase(ff[t]);
                        }
                        t2f[i][j].clear();
                    }
                }
                else at++;
            }
        }
        return at;
    }
    int RunToEnd() {
        int time = 0;
        while (RunATcik()) {
            time++;
        }
        return time;
    }
    int Run(int time){
        while(time&&RunATcik())time--;
        return time;//如果time大于0说明time的时间内已经跑完了
    }
};
BOOST_PYTHON_MODULE(scoring)
{
    class_<net>("net")
    .def("clearAll", &net::clearAll)
    .def("readEdgeFromPython", &net::readEdgeFromPython)
    .def("readTaskFromPython", &net::readTaskFromPython)
    .def("setTask", &net::setTask)
    .def("getTaskFromCpp", &net::getTaskFromCpp)
    .def("Run", &net::Run)
    .def("RunToEnd",&net::RunToEnd)
    ;
}
