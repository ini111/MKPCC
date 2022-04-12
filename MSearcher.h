#pragma once
#include "Defines.h"
using namespace std;
class HeuriSearcher{
public:
	MCSRGraph &g;
	int k;
	int *core;
	int *seq;
	int *pos;
	int* sol;
	int solSz;

	HeuriSearcher(MCSRGraph &_g, int _k,	int *_core, int *_seq, int *_pos,int *_sol)
	:g(_g), k(_k), core(_core), seq(_seq), pos(_pos),sol(_sol),solSz(0)
	{
	}

	int coreHeuristic(){    
		int *deg = new int[g.nbvtx];
		MBitSet64 *isSol = new MBitSet64(g.nbvtx);
		int maxcore = 0;
		bool hit = false;

		for (int i = 0; i < g.nbvtx; i++) {		
			deg[i] = g.degree(i);
			seq[i] = i;
			core[i] = -1;
		}
		ListLinearHeap *linear_heap = new ListLinearHeap(g.nbvtx, g.nbvtx);
		linear_heap->init(g.nbvtx, g.nbvtx, seq, deg);
		for (int i = 0; i < g.nbvtx; i++) {
			int u, key;
			linear_heap->pop_min(u, key);
			if (key > maxcore) 
				maxcore = key;	
			seq[i] = u;
			core[u] = maxcore;
			pos[u] = i;
			if ( i + key + k >= g.nbvtx && !hit){
				int sz = i+1;
				linear_heap->get_ids_of_larger_keys(seq, sz, key);
				solSz=g.nbvtx-i;
				int cnt=0;							
				for (int j = i ; j < g.nbvtx; j++){//vertices after i is not ordered
					sol[cnt++] = seq[j];				
					isSol->set(seq[j]);
				}
				hit = true;
			}
			for (int j = g.pstart[u]; j < g.pstart[u + 1]; j++){
				if (core[g.edges[j]] == -1)
					linear_heap->decrement(g.edges[j]);
			}
		}
		//extend the heuristic solution.
		//compute degrees
		memset(deg, 0, sizeof(int) * g.nbvtx);	
		int totSat = 0;
		const int lim=solSz-k;
		for (int i = 0; i < solSz; i++){
			const int u = sol[i];
			for (int j = g.pstart[u]; j < g.pstart[u+1]; j++){
				const int nei = g.edges[j];
				if (isSol->test(nei)){
					deg[u]++;
				}
			}
			if (deg[u] == lim){
				totSat++;
			}
		}
		
		//extending the remaining vertices
		for (int i = g.nbvtx - 1 - solSz; i >= 0; i--){
			const int lim=solSz-k;
			const int u = seq[i];
			if (core[u] + k <= solSz) break;
			int cntNei = 0, cntSat = 0;
			for (int j = g.pstart[u]; j < g.pstart[u+1]; j++){
				int nei = g.edges[j];
				if (isSol->test(nei)){
					cntNei++;
					if (deg[nei] == lim){
						cntSat++;
					}
				}
			}
			//extend u
			if (cntNei > lim && cntSat == totSat){ 
				deg[u] = cntNei;
				sol[solSz++] = u;
				isSol->set(u);
				//update number of saturated vertices.			
				for (int j = g.pstart[u]; j < g.pstart[u+1]; j++){
					const int nei = g.edges[j];
					if (isSol->test(nei)){
						deg[nei]++;
					}
				}
				//recount satu vertices
				totSat = 0;
				for (int j = 0; j < solSz; j++){				
					if (deg[sol[j]] == lim+1){
						totSat++;
					}
				}
			}
		}
		delete linear_heap;
		delete isSol;
		delete[] deg;
		return maxcore;
	}
};

extern int k,bestSz,*bestSol, maxsec, optimal;
extern long long int branches;
extern int rule1, rule2, rule3, rule4, rule7, rule8, rule8_0, rule9, rule9_0, rule9_1, rule9_2, rule11, rule12, rule1_1, rule2_2, rule3_3, rule4_4;
#include "MRandSet.h"
#include "MStack.h"
#include "MGraph.h"
using PlexStack = Stack<int>;
using VtxSet = RandSet<int>;
struct ExactSearcher
{
	MBitGraph *bg;
	const MCSRGraph &subg;
	int *neiInP;
	int *neiInG;
	bool stop;
	bool stopable;
	PlexStack *plex;
	VtxSet *cand1;
	VtxSet *cand2;
	VtxSet *CandB;
	const uint8_t* const adjMtx;
	int* const commMtx;
	int* const conflict;
	int* visSubG;
	int depth;
	int depthLim;
	clock_t startClk;
	ExactSearcher(const MCSRGraph &_subg, PlexStack *_plex, VtxSet *_cand1, VtxSet *_cand2,int *_neiInP, int *_neiInG, uint8_t* _adjMtx, int* _commMtx, int* _conflict, clock_t _startClk)
	:subg(_subg),plex(_plex),cand1(_cand1),cand2(_cand2),depth(0),depthLim(k/2),stop(false),stopable(true)
	,neiInP(_neiInP),neiInG(_neiInG),adjMtx(_adjMtx),commMtx(_commMtx),conflict(_conflict),startClk(_startClk)
	{
		CandB = new VtxSet(CAND_LIMIT);
		visSubG = new int[CAND_LIMIT];

		bg = new MBitGraph(_subg);
	}

	int interrupt() {
		if ((double)(clock() - startClk) / CLOCKS_PER_SEC > maxsec) {
			optimal = 0;
			return 1;
		}
		return 0;
	}

	bool isAdjMtx(const int v1,const int v2)
	{
		return adjMtx[v1*subg.nbvtx+v2];
	}

	void addG(const int u){
		for (int i = subg.pstart[u]; i < subg.pstart[u+1]; i++)
		{
			const int nei = subg.edges[i];
			neiInG[nei]++;
			if(stopable&&depth<depthLim){
				for (int j = i+1; j < subg.pstart[u+1]; j++)
				{
					const int nei2 = subg.edges[j];
					commMtx[nei*subg.nbvtx+nei2]++;
					commMtx[nei2*subg.nbvtx+nei]++;
				}
			}
		}
	}
	void subG(const int u){
		for (int i = subg.pstart[u]; i < subg.pstart[u+1]; i++)
		{
			const int nei = subg.edges[i];
			neiInG[nei]--;
			if(stopable&&depth<depthLim){
				for (int j = i+1; j < subg.pstart[u+1]; j++)
				{
					const int nei2 = subg.edges[j];
					commMtx[nei*subg.nbvtx+nei2]--;
					commMtx[nei2*subg.nbvtx+nei]--;
				}
			}
		}
	}

	void addP(const int u){
		for (int i = subg.pstart[u]; i < subg.pstart[u+1]; i++)
		{
			const int nei = subg.edges[i];
			neiInP[nei]++;
		}
	} 
	void subP(const int u){
		for (int i = subg.pstart[u]; i < subg.pstart[u+1]; i++)
		{
			const int nei = subg.edges[i];
			neiInP[nei]--;
		}
	}

	ExactSearcher* cand1ToPlex(const int v)
	{
		plex->push(v);
		cand1->remove(v);
		addP(v);
		return this;
	}

	ExactSearcher* plexToCand1()
	{
		assert(plex->sz > 0);
		const int u = plex->top();
		cand1->add(u);
		plex->pop();
		subP(u);
		return this;
	}

	int cand2ToPlex(const int v)
	{
		cand2->remove(v);
		plex->push(v);
		addP(v);
		return v;
	}

	ExactSearcher* plexToCand2()
	{
		assert(plex->sz > 0);
		const int v = plex->top();
		cand2->add(v);
		plex->pop();
		subP(v);
		return this;
	}

	ExactSearcher* cand1Move(const int v)
	{
		cand1->remove(v);
		subG(v);
		return this;
	}

	ExactSearcher* cand1Add(const int v)
	{
		cand1->add(v);
		addG(v);
		return this;
	}

	void cand2Move(const int v)
	{
		cand2->remove(v);
		subG(v);
	}

	ExactSearcher* cand2Add(const int v)
	{
		cand2->add(v);
		addG(v);
		return this;
	}

	ExactSearcher* updateCand1Fake(int& recCand1){
		int rec = cand1->sz;
		for(int i = 0; i < cand1->sz;)
		{
			int ele = cand1->members[i];
			if((!canFormPlex(ele))){
				cand1->fakeRemove(ele);
				subG(ele);
			}
			else ++i;
		}
		rec -= cand1->sz;
		recCand1 += rec;
		return this;
	}

	ExactSearcher* updateCand2Fake(int& recCand2){
		int rec = cand2->sz;
		for(int i = 0; i < cand2->sz;)
		{
			int ele = cand2->members[i];
			if((!canFormPlex(ele))){
				cand2->fakeRemove(ele);
				subG(ele);
			}
			else ++i;
		}
		rec -= cand2->sz;
		recCand2 += rec;
		return this;
	}

	//Check if plex+u is a k-plex
	bool canFormPlex(const int u)
	{
		if (neiInP[u] + k < plex->sz + 1 || neiInG[u] + k <= bestSz)
			return false;
		for (int i = 0; i < plex->sz; i++)
		{
			const int v = plex->members[i];
			if (stopable && commMtx[u*subg.nbvtx+v] < bestSz+1-2*k+2-2*isAdjMtx(v, u)) return false;
			if (neiInP[v] + k == plex->sz && !isAdjMtx(v, u))
			{ //v is saturated by v,u are not neighbors
				return false;
			}
			if(conflict[v*subg.nbvtx+u])
				return false;
		}
		return true;
	}

	static bool cmp(pair<int, int> a, pair<int, int> b) {
		if(a.second == b.second)
			return a.first < b.first;
		return a.second < b.second;
	}

	bool kplex_PUB() {
		CandB->clear();
		for(int i = 0; i < cand1->sz; i++) {
			int u = cand1->members[i];
			CandB->add(u);
		}
		for(int i = 0; i < cand2->sz; i++) {
			int u = cand2->members[i];
			CandB->add(u);
		}
		int PUB = plex->sz;
		vector<pair<int, int> > ord_P;
		for(int i = 0; i < plex->sz; i++) {
			int u = plex->members[i];
			ord_P.push_back(make_pair(u, neiInG[u]));
		}
		sort(ord_P.begin(), ord_P.end(), cmp);
		for(auto PP : ord_P) {
			int u = PP.first;
			int NotAdj = 0;
			for(int j = CandB->sz-1; j >= 0; j--) {
				int v = CandB->members[j];
				if(!isAdjMtx(u, v)) {
					CandB->remove(v);
					NotAdj++;
				}
			}
			PUB += min(NotAdj, neiInP[u]+k-plex->sz);
			if(PUB > bestSz)
				return true;
		}
		if(PUB+CandB->sz > bestSz)
			return true;
		return false;
	}

	void reduceCoPlex(int &popcnt1, int &popcnt2, int &recReCand1, int &recReCand2) {
		for(int i = 0; i < cand1->sz; ) {
			const int ele = cand1->members[i];
			const int NotNei = cand1->sz+cand2->sz+plex->sz-neiInG[ele];
			const int MaxNot = k-(plex->sz-neiInP[ele]);
			if(neiInP[ele] == plex->sz && (NotNei == 1 || NotNei == 2)) {
				cand1ToPlex(ele);
				popcnt1++;
				rule1_1++;
			}
			else if(neiInP[ele] == plex->sz-1 && NotNei == 2 && checkPlex(ele)) {
				cand1ToPlex(ele);
				popcnt1++;
				rule12++;
			}

			else if(neiInP[ele] == plex->sz && NotNei <= k && checkNei(ele)) {
				cand1ToPlex(ele);
				popcnt1++;
				rule2_2++;
			}
			else if(neiInP[ele] == plex->sz && NotNei == k+1 && checkNei(ele)) {
				cand1ToPlex(ele);
				popcnt1++;
				rule3_3++;
			}
			else if(neiInP[ele] == plex->sz && NotNei == 3 && checkTrangle(ele)) {
				cand1ToPlex(ele);
				popcnt1++;
				rule4_4++;
			}
			else 
				++i;
		}

		for(int i = 0; i < cand2->sz; ) {
			const int ele = cand2->members[i];
			const int NotNei = cand1->sz+cand2->sz+plex->sz-neiInG[ele];
			const int MaxNot = k-(plex->sz-neiInP[ele]);
			if(neiInP[ele] == plex->sz-1 && NotNei == 2 && checkPlex(ele)) {
				cand2ToPlex(ele);
				popcnt2++;
				rule12++;
			}
			else
				++i;
		}
			
		updateCand1Fake(recReCand1);
		updateCand2Fake(recReCand2);
	}

	void recoverCoPlex(int &popcnt1, int &popcnt2, int &recReCand1, int &recReCand2) {
		cand1->fakeRecoverAdd(recReCand1, this);
		while(popcnt1--)
			plexToCand1();
		cand2->fakeRecoverAdd(recReCand2, this);
		while(popcnt2--) 
			plexToCand2();
	}


	bool checkNei(int u) {
		int notSat = 0;
		for(int i = 0; i < cand1->sz; ++i) {
			int ele = cand1->members[i];
			if(!isAdjMtx(u, ele) && u != ele) {
				if(subg.nbvtx-neiInG[ele] > k) {
					notSat++;
					if(notSat > 1)
						return false;
				}
			}
		}
		for(int i = 0; i < cand2->sz; ++i) {
			int ele = cand2->members[i];
			if(!isAdjMtx(u, ele) && u != ele) {
				if(subg.nbvtx-neiInG[ele] > k) {
					notSat++;
					if(notSat > 1)
						return false;
				}
			}
		}
		return true;
	}

	bool checkTrangle(int u) {
		vector<int> NotNei;
		for(int i = 0; i < cand1->sz; ++i) {
			int ele = cand1->members[i];
			if(!isAdjMtx(u, ele) && u != ele) 
				NotNei.emplace_back(ele);
		}
		for(int i = 0; i < cand2->sz; ++i) {
			int ele = cand2->members[i];
			if(!isAdjMtx(u, ele) && u != ele) 
				NotNei.emplace_back(ele);
		}
		if(NotNei.size() == 2) {
			int ele1 = NotNei[0], ele2 = NotNei[1];
			if(!isAdjMtx(ele1, ele2)) 
				return true;
		}
		return false;
	}

	bool checkPlex(int u) {
		for(int i = 0; i < plex->sz; i++) {
			int ele = plex->members[i];
			if(!isAdjMtx(u, ele)) {
				if(plex->sz-neiInP[ele] < k)
					return true;
				else
					return false;
			}
		}
		return false;
	}

	vector<int> find_cycle_path(int u) {
		vector<int> pre, back, path;
		pre.emplace_back(u);
		back.emplace_back(u);
		for(int v = 0; v < subg.nbvtx; ++v) {
			if(!isAdjMtx(u, v) && u != v) {
				if(pre.size() == 1)
					pre.emplace_back(v);
				else
					back.emplace_back(v);
			} 
		}
		int flag = 1;
		for(int i = 1; i < pre.size(); ++i) {
			int v = pre[i];
			if(u == v && visSubG[v]) 
				return pre;
			if(visSubG[v] || neiInP[v] != plex->sz) {
				flag = 0;
				break;
			}
			if(subg.nbvtx-neiInG[v] != 3) 
				break;
			visSubG[v] = 1;
			for(int ele = 0; ele < subg.nbvtx; ++ele) {
				if(!isAdjMtx(v, ele) && ele != v && ele != pre[i-1]) {
					pre.emplace_back(ele);
					break;
				}
			}
		}
		for(int i = 1; i < back.size() && flag == 1; ++i) {
			int v = back[i];
			if(visSubG[v] || neiInP[v] != plex->sz) {
				flag = 0;
				break;
			}
			if(subg.nbvtx-neiInG[v] != 3)
				break;
			visSubG[v] = 1;
			for(int ele = 0; ele < subg.nbvtx; ++ele) {
				if(!isAdjMtx(v, ele) && ele != v && ele != back[i-1]) {
					back.emplace_back(ele);
					break;
				}
			}
		}
		if(flag) {
			for(int i = pre.size()-1; i >= 0; --i)
				path.emplace_back(pre[i]);
			for(int i = 1; i < back.size(); ++i)
				path.emplace_back(back[i]);
		}
		return path;
	}

	void reduce_cycle_path() {
		memset(visSubG, 0, sizeof(int)*subg.nbvtx);
		cand1ToPlex(0);
		visSubG[0] = 1;
		for(int u = 1; u < subg.nbvtx; u++) {
			if(!visSubG[u] && neiInP[u] == plex->sz && subg.nbvtx-neiInG[u] == 3) {
				vector<int> path;
				path = find_cycle_path(u);
				if(!path.size())
					continue;
				if(path[0] == path[path.size()-1]) {
					if(k == 2) {
						for(int i = 1; i < path.size()-1; ++i) {
							if(i%3 == 1 || i%3 == 2) 
								cand1ToPlex(path[i]);
							rule7++;
						}
					}
					else if(k >= 3) {
						if(neiInG[path[0]] == subg.nbvtx-3) {
							cand1ToPlex(path[0]);
							rule8_0++;
						}
						for(int i = 1; i < path.size()-1; ++i)
							cand1ToPlex(path[i]);
						rule8++;
					}
				} 
				else if(neiInG[path[0]] == subg.nbvtx-2 && neiInG[path[path.size()-1]] == subg.nbvtx-2) {
					if(k >= 3) {
						for(int i = 0; i < path.size(); ++i)
							cand1ToPlex(path[i]);
						rule9_0++;
					}
				}
				else if(neiInG[path[0]] == subg.nbvtx-2 && neiInG[path[path.size()-1]] != subg.nbvtx-2) {
					if(k >= 3) {
						for(int i = 0; i < path.size()-1; ++i)
							cand1ToPlex(path[i]);
						rule9_1++;
					}
				}
				else if(neiInG[path[0]] != subg.nbvtx-2 && neiInG[path[path.size()-1]] == subg.nbvtx-2) {
					if(k >= 3) {
						for(int i = 1; i < path.size(); ++i)
							cand1ToPlex(path[i]);
						rule9_2++;
					}
				}
				else if(path.size() >= 4) {
					if(k >= 3) {
						for(int i = 1; i < path.size()-1; ++i)
							cand1ToPlex(path[i]);
						rule9++;
					}
				}
			}
		}
	}

	void Reduce() {
		reduce_cycle_path();
		for(int i = 0; i < cand1->sz; ) {
			int ele = cand1->members[i];
			int NotNei = subg.nbvtx-neiInG[ele];
			if(neiInP[ele] == plex->sz && (NotNei == 1 || NotNei == 2)) {
				cand1ToPlex(ele);
				rule1++;
			}
			else if(neiInP[ele] == plex->sz && NotNei <= k && checkNei(ele)) {
				cand1ToPlex(ele);
				rule2++;
			}
			else if(neiInP[ele] == plex->sz && NotNei == k+1 && checkNei(ele)) {
				cand1ToPlex(ele);
				rule3++;
			}
			else if(neiInP[ele] == plex->sz && NotNei == 3 && checkTrangle(ele)) {
				cand1ToPlex(ele);
				rule4++;
			}
			else if(neiInP[ele] == plex->sz-1 && NotNei == 2 && checkPlex(ele)) {
				cand1ToPlex(ele);
				rule11++;
			}
			else
				++i;
		}
	}

	//branch
	void hop2Search(int res){
		if(interrupt())
			return ;
		if(stopable&&stop)return;
		branches++;

		int popcnt1 = 0, popcnt2 = 0;
		int recReCand1 = 0, recReCand2 = 0;
		reduceCoPlex(popcnt1, popcnt2, recReCand1, recReCand2);
		res -= popcnt2;

		//bound
		int minnei=INT_MAX-1000,maxnei=INT_MIN+1000; int pivot;
		for(int i=0;i<plex->sz;++i){
			const int ele=plex->members[i];
			const int nei=neiInG[ele];
			if(nei<minnei) minnei=nei;
		}
		if (minnei + k <= bestSz) goto RECOVER2;
		if(plex->sz+cand1->sz+std::min(res,cand2->sz)<=bestSz) goto RECOVER2;
		if(!cand2->sz){depth++,hop1Search(),depth--;goto RECOVER2;}

		for(int i=0;i<cand2->sz;++i){
			const int ele=cand2->members[i];
			const int nei=neiInG[ele];
			if(nei<minnei) minnei=nei;
			if(nei>maxnei) maxnei=nei;
		}
		if(maxnei + k <= bestSz){
			const int recCand2=cand2->sz;
			cand2->sz=0;
			for(int i=0;i<recCand2;++i)subG(cand2->members[i]);
			depth++,hop1Search(),depth--;
			for(int i=0;i<recCand2;++i)addG(cand2->members[i]);
			cand2->sz=recCand2;
			goto RECOVER2;
		}
		for(int i=0;i<cand1->sz;++i){
			const int ele=cand1->members[i];
			const int nei=neiInG[ele];
			if(nei<minnei) minnei=nei;
		}
		if (minnei + k >= plex->sz + cand1->sz + cand2->sz)
		{
			bestSz = plex->sz + cand1->sz + cand2->sz;
			stop=true;
			memcpy(bestSol,plex->members,plex->sz*sizeof(int));
			memcpy(&bestSol[plex->sz],cand1->members,cand1->sz*sizeof(int));
			memcpy(&bestSol[plex->sz+cand1->sz],cand2->members,cand2->sz*sizeof(int));
			goto RECOVER2;
		}

		if(!kplex_PUB())
			goto RECOVER2;

		//branch
		pivot=cand2->members[cand2->sz-1];
		cand2ToPlex(pivot);
		if(res==1){
			const int recCand2=cand2->sz;
			cand2->sz=0;
			for(int i=0;i<recCand2;++i)subG(cand2->members[i]);
			depth++,hop1Search(),depth--;
			for(int i=0;i<recCand2;++i)addG(cand2->members[i]);
			cand2->sz=recCand2;
		}
		else{
			depth++,hop2Search(res-1),depth--;
		}
		plexToCand2();

		cand2Move(pivot);
		depth++,hop2Search(res),depth--;
		cand2Add(pivot);

	RECOVER2:
		recoverCoPlex(popcnt1, popcnt2, recReCand1, recReCand2);
	}
	
	//branch
	void hop1Search()
	{
		if(interrupt())
			return ;
		if(stopable&&stop)return;
		branches++;

		int popcnt1 = 0, popcnt2 = 0;
		int recReCand1 = 0, recReCand2 = 0;
		// Reduction based on complement graph
		reduceCoPlex(popcnt1, popcnt2, recReCand1, recReCand2);

		//bound
		int minnei=INT_MAX-1000,maxnei=INT_MIN+1000; int pivot;
		if (plex->sz + cand1->sz <= bestSz) goto RECOVER1;
		if (plex->sz > bestSz){
			bestSz = plex->sz;
			stop=true;
			memcpy(bestSol,plex->members,bestSz*sizeof(int));
			goto RECOVER1;
		}
		if (!cand1->sz) goto RECOVER1;
		for(int i=0;i<plex->sz;++i){
			const int ele=plex->members[i];
			const int nei=neiInG[ele];
			if(nei<minnei) minnei=nei;
		}
		if (minnei + k <= bestSz) goto RECOVER1;
		for(int i=0;i<cand1->sz;++i){
			const int ele=cand1->members[i];
			const int nei=neiInG[ele];
			if(nei<minnei) minnei=nei;
			if(nei>maxnei) maxnei=nei;
		}
		if(maxnei + k <= bestSz) goto RECOVER1;
		if (minnei + k >= plex->sz + cand1->sz)
		{
			bestSz = plex->sz + cand1->sz;
			stop=true;
			memcpy(bestSol,plex->members,plex->sz*sizeof(int));
			memcpy(bestSol+plex->sz,cand1->members,cand1->sz*sizeof(int));
			goto RECOVER1;
		}

		if(!kplex_PUB())
			goto RECOVER1;

		//branch
		pivot=cand1->members[cand1->sz-1];
		//In the first branch, select pivot
		
		cand1ToPlex(pivot);
		depth++,hop1Search(),depth--;
		plexToCand1();

		//In the second branch, remove pivot
		cand1Move(pivot);
		depth++,hop1Search(),depth--;
		cand1Add(pivot);
	RECOVER1:
		// cand1->fakeRecoverAdd(recReCand1,this);
		// while(popcnt1--) plexToCand1();
		recoverCoPlex(popcnt1, popcnt2, recReCand1, recReCand2);
	}
};