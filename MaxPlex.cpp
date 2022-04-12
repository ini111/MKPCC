#include "LinearHeap.h"
#include "MGraph.h"
#include "MSearcher.h"
char filename[LEN_LIMIT];
int k,bestSz,*bestSol, optimal = 1, maxsec = 1800;
long long int branches;
int rule1, rule2, rule3, rule4, rule7, rule8, rule8_0, rule9, rule9_0, rule9_1, rule9_2, rule11, rule12, rule1_1, rule2_2, rule3_3, rule4_4;
MCSRGraph orG; 		//input graph
MCSRGraph coreG;	//core graph
MCSRGraph kernelG;  //kernel graph
MCSRGraph subG;	    //decomposed subgraph

//date structure for subgraph
vector<int> neibors;
vector<int> filtered;
vector<uint8_t> visited;
vector<int> counter;
vector<int> blk; //vstart and its right 1-hop and 2-hop neighbors
vector<uint8_t> inBlk;
PlexStack plex(PLEX_LIMIT);
VtxSet cand1(CAND_LIMIT);
VtxSet cand2(CAND_LIMIT);
vector<int> neiInP(CAND_LIMIT,0);
vector<int> neiInG(CAND_LIMIT);
uint8_t adjMtx[CAND_LIMIT*CAND_LIMIT];
int commMtx[CAND_LIMIT*CAND_LIMIT];
int conflict[CAND_LIMIT*CAND_LIMIT];
int conflict_tmp[CAND_LIMIT*CAND_LIMIT];
int *tmpG_kernelG, *kernelG_tmpG;
int *hop2vis, tmpGSz;

int interrupt(clock_t startClk) {
	if ((double)(clock() - startClk) / CLOCKS_PER_SEC > maxsec) {
		optimal = 0;
		return 1;
	}
	return 0;
}


template<typename Pred>
int hop2Count(const MCSRGraph &g,const int vstart,Pred &&pred) {
	memset(tmpG_kernelG, -1, sizeof(int)*g.nbvtx);
	memset(kernelG_tmpG, -1, sizeof(int)*g.nbvtx);
	memset(hop2vis, -1, sizeof(int)*g.nbvtx);
	vector<int> hop1, hop2;
	for(int i = g.pstart[vstart]; i < g.pstart[vstart+1]; i++) {
		int u = g.edges[i];
		if(pred(vstart, u)) {
			hop2vis[u] = 0;
			hop1.emplace_back(u);
		}
	}
	if(bestSz+1-2*k <= 0) {
		for(auto u : hop1)
			hop2.emplace_back(u);
		hop2vis[vstart] = 0;
		for(auto u : hop1) {
			for(int j = g.pstart[u]; j < g.pstart[u+1]; j++) {
				int v = g.edges[j];
				if(pred(vstart, v) && hop2vis[v] == -1) {
					hop2.emplace_back(v);
					hop2vis[v] = 0;
				}
			}
		}
	}
	else {
		for(auto u : hop1) {
			for(int j = g.pstart[u]; j < g.pstart[u+1]; j++) {
				int v = g.edges[j];
				if(pred(vstart, v) && hop2vis[v] >= 0) {
					hop2vis[v]++;
					if(hop2vis[v] == bestSz+1-2*k)
						hop2.emplace_back(v);
				}
			}
		}

		for(auto u : hop1)
			hop2vis[u] = -2;
		hop2vis[vstart] = -2;

		int hop1Sz = hop2.size();
		for(int i = 0; i < hop1Sz; i++) {
			int u = hop2[i];
			for(int j = g.pstart[u]; j < g.pstart[u+1]; j++) {
				int v = g.edges[j];
				if(pred(vstart, v) && hop2vis[v] != -2) {
					if(hop2vis[v] == -1)
						hop2vis[v] = 1;
					else
						hop2vis[v]++;
					if(hop2vis[v] == bestSz+3-2*k)
						hop2.emplace_back(v);
				}
			}
		}
	}
	hop2.emplace_back(vstart);
	int tmpGIdx = 0;
	for(auto u : hop2) {
		kernelG_tmpG[u] = tmpGIdx;
		tmpG_kernelG[tmpGIdx++] = u;
	}
	return tmpGIdx;
}

//Decompose a local graph contains vstart and its 1a2hop-neighbors from the global graph
template<typename Pred>
int decompose(const MCSRGraph &g,const int vstart,const int idx, vector<int> &neibors_1a2hop,Pred &&pred){
	//Calculate the induced subgraph of {vstart, 1hop, 2hop}.
	const int kernelSz = hop2Count(g, vstart, pred);
	tmpGSz = kernelSz;
	if(kernelSz <= bestSz)
		return 0;
	//collect 1 hop neigbors
	visited[vstart]  = 1;
	inBlk[vstart]=true;
	for(int j = g.pstart[vstart]; j < g.pstart[vstart+1]; j++){
		const int nei = g.edges[j];
		if(pred(vstart,nei)&&!visited[nei] && kernelG_tmpG[nei] != -1)//1-hop right-neighbor
		{
			visited[nei] = 1;
			neibors_1a2hop.emplace_back(nei);
			inBlk[nei]=true;
		}
	}
	int initSz = neibors_1a2hop.size();
	if(initSz+k<=bestSz){
		visited[vstart]=false;
		inBlk[vstart]=false;
		for(int i=0;i<initSz;++i){
			const int ele=neibors_1a2hop[i];
			visited[ele]=false;
			inBlk[ele]=false;
		}
		neibors_1a2hop.clear();
		return 0;
	}
	const int lim1=(bestSz+1-2*k);
	const int lim2=(bestSz+3-2*k);
	const int lim11=(bestSz+1-3*k);
	const int lim12=(bestSz+3-3*k);
	const int lim22=(bestSz+5-3*k);
	const int lim23=(bestSz+7-3*k);
	memset(commMtx,0,sizeof(int)*kernelSz*kernelSz); //a matrix of kernelG
	memset(adjMtx,0,sizeof(uint8_t)*kernelSz*kernelSz);
	memset(conflict_tmp, 0, sizeof(int)*kernelSz*kernelSz);
	#define setAdj(u,v) adjMtx[(kernelG_tmpG[u])*kernelSz+(kernelG_tmpG[v])]=1,adjMtx[(kernelG_tmpG[v])*kernelSz+(kernelG_tmpG[u])]=1
	#define resetAdj(u,v) adjMtx[(kernelG_tmpG[u])*kernelSz+(kernelG_tmpG[v])]=0,adjMtx[(kernelG_tmpG[v])*kernelSz+(kernelG_tmpG[u])]=0
	#define incComm(u,v) commMtx[(kernelG_tmpG[u])*kernelSz+(kernelG_tmpG[v])]++,commMtx[(kernelG_tmpG[v])*kernelSz+(kernelG_tmpG[u])]++
	#define decComm(u,v) commMtx[(kernelG_tmpG[u])*kernelSz+(kernelG_tmpG[v])]--,commMtx[(kernelG_tmpG[v])*kernelSz+(kernelG_tmpG[u])]--
	#define getComm(u,v) commMtx[(kernelG_tmpG[u])*kernelSz+(kernelG_tmpG[v])]
	#define getAdj(u,v) adjMtx[(kernelG_tmpG[u])*kernelSz+(kernelG_tmpG[v])]
	#define setConflict(u,v) conflict_tmp[(kernelG_tmpG[u])*kernelSz+(kernelG_tmpG[v])]=1,conflict_tmp[(kernelG_tmpG[v])*kernelSz+(kernelG_tmpG[u])]=1

	//third-order reduction
	//init adjMtx
	{
		const int ele=vstart;
		const int end=g.pstart[ele+1];
		for(int j=g.pstart[ele];j<end;++j){
			const int nei=g.edges[j];
			if(nei>ele)break;
			if(!inBlk[nei])continue;
			setAdj(ele,nei);
		}
	}
	for(int i=0;i<initSz;++i){
		const int ele=neibors_1a2hop[i];
		const int end=g.pstart[ele+1];
		for(int j=g.pstart[ele];j<end;++j){
			const int nei=g.edges[j];
			if(nei>ele)break;
			if(!inBlk[nei])continue;
			setAdj(ele,nei);
		}
	}

	//init common neighbors of 1-hop
	for(int i=0;i<initSz;++i){
		const int ele=neibors_1a2hop[i];
		const int end=g.pstart[ele+1];
		for(int j=g.pstart[ele];j<end;++j){
			const int nei1=g.edges[j];
			if(!inBlk[nei1])continue;
			for(int k=j+1;k<end;++k){
				const int nei2=g.edges[k];
				if(!inBlk[nei2])continue;
				incComm(nei1,nei2);
			}
		}
	}

	//find conflicting (u,v) in 1-hop
	int filterSz=0;
	bool flag;
	do{
		flag=false;
		for(int i=0;i<initSz;++i){
			const int ele=neibors_1a2hop[i];
			if(!inBlk[ele])continue;
			if(getComm(vstart,ele)<lim1){
				flag=true;
				filtered.push_back(ele);
				inBlk[ele]=false;
				filterSz++;
				const int end=g.pstart[ele+1];
				for(int j=g.pstart[ele];j<end;++j){
					const int nei1=g.edges[j];
					if(!inBlk[nei1]||!getAdj(ele,nei1))continue;
					for(int k=j+1;k<end;++k){
						const int nei2=g.edges[k];
						if(!inBlk[nei2]||!getAdj(ele,nei2))continue;
						decComm(nei1,nei2);
					}
				}
			}
		}
		if(initSz-filterSz<=bestSz-k)break;
		for(int i=0;i<initSz;++i){
			const int ele=neibors_1a2hop[i];
			if(!inBlk[ele])continue;
			for(int j=i+1;j<initSz;++j){
				const int nei=neibors_1a2hop[j];
				if(!inBlk[nei])
					continue;
				if(!getAdj(ele, nei)) {
					if(getComm(ele, nei) < lim12)
						setConflict(ele, nei);
					continue;
				}
				//if(!inBlk[nei]||!getAdj(ele,nei))continue;
				if(getComm(ele,nei)<lim11){
					flag=true;
					resetAdj(ele,nei);
					setConflict(ele, nei);
					for(int j=kernelG.pstart[ele];j<kernelG.pstart[ele+1];++j){
						const int comm=kernelG.edges[j];
						if(!inBlk[comm])continue;
						if(getAdj(ele,comm)&&getAdj(nei,comm)){
							decComm(comm,ele);
							decComm(comm,nei);
						}
					}
				}
			}
		}
	}while(flag);
	if(initSz-filterSz<=bestSz-k){
		visited[vstart]=false;
		inBlk[vstart]=false;
		for(int i=0;i<initSz;++i){
			const int ele=neibors_1a2hop[i];
			visited[ele]=false;
			inBlk[ele]=false;
		}
		neibors_1a2hop.clear();
		filtered.clear();
		return 0;
	}
	int hopSz=initSz-filterSz;
	int cursor=0;
	for(int i=0;i<initSz;++i){
		const int ele=neibors_1a2hop[i];
		if(inBlk[ele]){
			neibors_1a2hop[cursor++]=ele;
		}
	}
	neibors_1a2hop.resize(hopSz);

	//collect 2-hop neigbors
	for(const auto nei1 : neibors_1a2hop){
		for (int j = g.pstart[nei1]; j < g.pstart[nei1+1]; j++)
		{
			const int nei2 = g.edges[j];
			if (pred(vstart, nei2)&&!visited[nei2] && kernelG_tmpG[nei2] != -1){
				if(!counter[nei2]){
					neibors.emplace_back(nei2);
				}
				counter[nei2]++;
			}
		}
	}
	neibors_1a2hop.emplace_back(vstart);
	swap(neibors_1a2hop[0], neibors_1a2hop[neibors_1a2hop.size() - 1]);
	hopSz++;
	cursor++;
	//In fact, neibors_1a2hop contains the vstart at the first
	for (int v : neibors) {
		if (counter[v] >= lim2) {	//the number of common neighbors with vstart >= lb-2*k+3
			neibors_1a2hop.emplace_back(v);
			inBlk[v]=true;
		}
		counter[v] = 0;
	}

	neibors.clear();
	int blkSz=neibors_1a2hop.size();
	for(int i=hopSz;i<blkSz;++i){
		const int ele=neibors_1a2hop[i];
		for(int j=g.pstart[ele];j<g.pstart[ele+1];++j){
			const int nei=g.edges[j];
			if(inBlk[nei])setAdj(ele,nei);
		}
	}
	//reinit common neighbors in 1-hop for 2-hop
	for(int i=1;i<hopSz;++i){
		const int ele=neibors_1a2hop[i];
		const int end=g.pstart[ele+1];
		for(int j=g.pstart[ele];j<end;++j){
			const int nei2=g.edges[j];
			if(!inBlk[nei2]||visited[nei2])continue;
			for(int k=g.pstart[ele];k<end;++k){
				const int neix=g.edges[k];
				if(!inBlk[neix])continue;
				if(visited[neix]|| neix<nei2) incComm(nei2,neix);
			}
		}
	}

	do{
		flag=false;
		for(int i=hopSz;i<blkSz;++i){
			const int ele=neibors_1a2hop[i];
			for(int j=1;j<hopSz;++j){
				const int nei=neibors_1a2hop[j];
				if(!getAdj(ele,nei)) {
					if(getComm(ele, nei) < lim22)
						setConflict(ele, nei);
					continue;
				}
				if(getComm(ele,nei)<lim12){
					flag=true;
					resetAdj(ele,nei);
					setConflict(ele, nei);
					decComm(vstart,ele);
					for(int k=kernelG.pstart[ele];k<kernelG.pstart[ele+1];++k){
						const int comm=kernelG.edges[k];
						if(!inBlk[comm])continue;
						if(getAdj(ele,comm)&&getAdj(nei,comm)){
							decComm(comm,ele);
						}
						// !getAdj(ele,vstart)&&getAdj(nei,vstart)    decComm(vstart,ele)
					}					
				}
			}
		}
		for(int i=hopSz;i<blkSz;++i){
			const int ele=neibors_1a2hop[i];
			if(getComm(vstart,ele)<lim2){
				inBlk[ele]=false;
				filterSz++;
			}
		}
	}while(flag);
	for(int i=hopSz;i<blkSz;++i){
		const int ele=neibors_1a2hop[i];
		if(inBlk[ele]){
			neibors_1a2hop[cursor++]=ele;
		}
	}
	neibors_1a2hop.resize(cursor);
	blkSz=cursor;
	for(int i=hopSz;i<blkSz;++i){
		const int ele=neibors_1a2hop[i];
		for(int j=i+1;j<blkSz;++j){
			const int ele2=neibors_1a2hop[j];
			if(!getAdj(ele,ele2)) {
				if(getComm(ele, ele2) < lim23)
					setConflict(ele, ele2);
				continue;
			}
			if(getComm(ele,ele2)<lim22){
				resetAdj(ele,ele2);
				setConflict(ele, ele2);
			}
		}
	}
	for(int i=0;i<hopSz;++i) visited[neibors_1a2hop[i]]=0;
	for (auto v : filtered ) visited[v] = 0;
	filtered.clear();
	if(blkSz<=bestSz){
		for(const auto v : neibors_1a2hop) inBlk[v]=false;
		neibors_1a2hop.clear();
		hopSz=0;
	}
	return hopSz;
}

//Build edges among the local nodes
void buildSubgraph(const MCSRGraph &kernelG,MCSRGraph &subG,const vector<int>& blk, const vector<uint8_t> &inBlk, const int hopSz){  
	const int blkSz=blk.size();
	//const int tmpGSz=kernelG.nbvtx-idx+1;
	subG.nbvtx = blkSz; subG.nbedges = 0;
    subG.pstart = new int[subG.nbvtx+1];
	subG.phop = new int[subG.nbvtx];
    subG.pstart[0] = 0;
	subG.edges = new int[kernelG.nbedges];
    int * const edges = subG.edges;
	//cout << "subG: " << blkSz << endl;
	memset(conflict, 0, sizeof(int)*tmpGSz*tmpGSz);
    for (int i = 0; i < blkSz; i++){
        const int ele = blk[i];
        subG.pstart[i+1] = subG.pstart[i];
		subG.phop[i] = subG.pstart[i];
		for(int j=0; j<blkSz ;++j ){
			const int nei=blk[j];
			if(adjMtx[kernelG_tmpG[ele]*tmpGSz+kernelG_tmpG[nei]]){
				if(j<hopSz)subG.phop[i]++;
				edges[subG.pstart[i+1]++] = j;
                subG.nbedges++;
			}
			if(conflict_tmp[kernelG_tmpG[ele]*tmpGSz+kernelG_tmpG[nei]]) 
				conflict[i*subG.nbvtx+j] = conflict[j*subG.nbvtx+i] = 1;
		}
	}
}

void KPX(){
	//reading
	int MaxSubG = 0;
	rule1 = rule2 = rule3 = rule4 = rule7 = rule8 = rule8_0 = rule9 = rule9_0 = rule9_1 = rule9_2 = rule11 = rule12 = rule1_1 = rule2_2 = rule3_3 = rule4_4 = 0;
	orG.fromBinaryFile(filename);
	double orDense = 0, coreDense = 0, kernelDense = 0;
	if(orG.nbvtx != 0)
		orDense=(double)2*orG.nbedges/((double)orG.nbvtx*(orG.nbvtx-1));
    printf("input graph n=%d m=%d d=%.3f (undirected)\n", orG.nbvtx, orG.nbedges, orDense);	

	int *core = new int[orG.nbvtx];
	int *dseq = new int[orG.nbvtx];
	int *dpos = new int[orG.nbvtx];
	bestSol = new int[orG.nbvtx]; bestSz = 0;
	int *new2ori = new int[orG.nbvtx]; //mapping for vertex renumbering

	//date structure for decomposition
	visited.assign(orG.nbvtx,0);
	counter.assign(orG.nbvtx, 0);
	inBlk.assign(orG.nbvtx,0);
	auto pred = [dpos](int v1 ,int v2){
		return dpos[v1] < dpos[v2];
	};
	//date structure for subgraph
	int *coreSub = new int[orG.nbvtx];
	int *dseqSub = new int[orG.nbvtx];
	int *dposSub = new int[orG.nbvtx]; 
	int *bestSolSub = new int[orG.nbvtx];

	clock_t startClk = clock();
	HeuriSearcher heuriSearcher(orG,k,core,dseq,dpos,bestSol);
	clock_t heuriClk = clock();

	int max_core=heuriSearcher.coreHeuristic(); int UB=max_core+k;
	bestSz = heuriSearcher.solSz;
	
	bool opt=(bestSz==UB)||peelReduction(orG,coreG,k,bestSz,core,dseq,dpos,new2ori);
	clock_t lvl1Clk = clock();
	
	if(coreG.nbvtx != 0)
		coreDense = (double)coreG.nbedges/((double)coreG.nbvtx*(coreG.nbvtx-1));
	printf("Core graph n=%d m=%d d=%.3f CoreTime=%.2f\n", coreG.nbvtx, coreG.nbedges/2, coreDense ,Utility::elapse_seconds(heuriClk, lvl1Clk));
	
	if(!opt){
		strongReduction(coreG, kernelG, k, heuriSearcher.solSz, new2ori);
		if(kernelG.nbvtx != 0)
			kernelDense = (double)kernelG.nbedges/((double)kernelG.nbvtx*(kernelG.nbvtx-1));
		printf("Kernal graph n:%d m:%d d=%.3f Kerneltime:%.2f\n", kernelG.nbvtx, kernelG.nbedges/2, kernelDense ,Utility::elapse_seconds(lvl1Clk, clock()));
		opt=(kernelG.nbvtx==UB);
	}
	clock_t lvl2Clk = clock();

	HeuriSearcher heuriKernelSearcher(kernelG,k,core,dseq,dpos,bestSolSub);
	max_core=heuriKernelSearcher.coreHeuristic();
	UB=min(UB,max_core+k);
	if(heuriKernelSearcher.solSz>bestSz){
		bestSz=heuriKernelSearcher.solSz;
		//swap(bestSol,bestSolSub);
		for (int i = 0; i < bestSz; i++) 
			bestSol[i] = new2ori[bestSolSub[i]];
	}

	int heuSize = bestSz;

	if(kernelDense <= 0.95){
		bestSz = max(2*k-2, bestSz);
		
		tmpG_kernelG = new int[kernelG.nbvtx];
		kernelG_tmpG = new int[kernelG.nbvtx];
		hop2vis = new int[kernelG.nbvtx];
		for(int idx = kernelG.nbvtx-1-bestSz; idx >= 0 ; idx--){
			if(interrupt(startClk))
				break;
			const int vstart=dseq[idx];
			if(core[vstart]+k<=bestSz)break;
			blk.clear();
			const int hopSz=decompose(kernelG,vstart,idx,blk,pred);
			const int blkSz=blk.size();
			const int hop2Sz=blkSz-hopSz;
			if(!blkSz)continue;
			//cout << "test: " << idx << "   " << hopSz << "   " << blkSz << "   " << bestSz << "   " << branches << "   " << Utility::elapse_seconds(startClk, clock()) << endl;
			MaxSubG = max(MaxSubG, blkSz);
			buildSubgraph(kernelG,subG,blk,inBlk,hopSz);

			HeuriSearcher heuriSubSearcher(subG,k,coreSub,dseqSub,dposSub,bestSolSub);
			const int UBSub=min(heuriSubSearcher.coreHeuristic()+k, hopSz+k);
			if(heuriSubSearcher.solSz>bestSz){
				bestSz = heuriSubSearcher.solSz; 
				for(int i = 0; i < bestSz; i++) 
					bestSol[i] = new2ori[blk[bestSolSub[i]]];
				cout<<bestSz<<endl;
			}
			else if(UBSub>bestSz){
				//sort and add cand1
				for (int j = 0; j < hopSz; j++){
					neiInG[j] = subG.degree(j);
					neibors.push_back(j);
				}
				sort(begin(neibors),end(neibors),[&](const int a,const int b){return dposSub[a]<dposSub[b];});
				for( const auto v : neibors) cand1.add(v); neibors.clear();
				//sort and add cand2
				for (int j = hopSz; j < blkSz; j++){
					neiInG[j] = subG.degree(j);
					neibors.push_back(j);
				}
				sort(begin(neibors),end(neibors),[&](const int a,const int b){return dposSub[a]<dposSub[b];});
				for( const auto v : neibors) cand2.add(v); neibors.clear();
				
				//build adjacency-matrix
				memset(adjMtx,0,sizeof(uint8_t)*subG.nbvtx*subG.nbvtx);
				for(int i=0;i< subG.nbvtx;++i){
					for(int j=subG.pstart[i];j<subG.pstart[i+1];++j){
						const int k=subG.edges[j];					
						adjMtx[i*subG.nbvtx+k]=1;
					}
				}

				//build commonNeighbors-matrix
				memset(commMtx,0,sizeof(int)*subG.nbvtx*subG.nbvtx);
				for(int i=0;i<blkSz;++i){
					for(int j=subG.pstart[i];j<subG.pstart[i+1];++j){
						const int nei1=subG.edges[j];
						for(int k=j+1;k<subG.pstart[i+1];++k){
							const int nei2=subG.edges[k];
							commMtx[nei1*subG.nbvtx+nei2]++;
							commMtx[nei2*subG.nbvtx+nei1]++;
						}
					}
				}

				for(int i = 0; i < blkSz; ++i) {
					for(int j = i+1; j < blkSz; ++j) {
						if(commMtx[i*subG.nbvtx+j] < bestSz+1-2*k+2-2*adjMtx[i*subG.nbvtx+j])
							conflict[i*subG.nbvtx+j] = conflict[j*subG.nbvtx+i] = 1;
					}
				}

				ExactSearcher exactSearcher(subG, &plex, &cand1, &cand2, neiInP.data(), neiInG.data(), adjMtx, commMtx, conflict, startClk);
				//Add u and some vertices to P
				exactSearcher.Reduce();
				exactSearcher.hop2Search(k-1);
				while(exactSearcher.plex->sz)
					exactSearcher.plexToCand1();
				cand1.clear();
				cand2.clear();
				
				if(exactSearcher.stop){
					for (int i = 0; i < bestSz; i++) { bestSol[i] = new2ori[blk[bestSol[i]]];}
					cout<<bestSz<<endl;
				}
			}
			for(const auto v : blk) inBlk[v]=false;
			subG.del();
			if(bestSz==UB)break;
		}
		delete[] kernelG_tmpG;
		delete[] tmpG_kernelG;
		delete[] hop2vis;
	}
	if(kernelDense > 0.95 || bestSz <= 2*k-2) {
		if(bestSz == 2*k-2) 
			bestSz = heuSize;
		for (int j = 0; j < kernelG.nbvtx; j++){
			neiInG[j] = kernelG.degree(j);
			cand1.add(dseq[kernelG.nbvtx-1-j]);
		}
		cout << heuSize << endl;
		//build adjacency-matrix
		memset(adjMtx,0,sizeof(uint8_t)*kernelG.nbvtx*kernelG.nbvtx);
		memset(conflict,0,sizeof(int)*kernelG.nbvtx*kernelG.nbvtx);
		for(int i=0;i< kernelG.nbvtx;++i){
			for(int j=kernelG.pstart[i];j<kernelG.pstart[i+1];++j){
				const int k=kernelG.edges[j];					
				adjMtx[i*kernelG.nbvtx+k]=1;
			}
		}
		ExactSearcher exactSearcher(kernelG, &plex, &cand1, &cand2, neiInP.data(), neiInG.data(), adjMtx, commMtx, conflict, startClk);
		exactSearcher.stopable=false;
		exactSearcher.hop1Search();
		if(exactSearcher.stop){
			for (int i = 0; i < bestSz; i++) bestSol[i] = new2ori[bestSol[i]];
			cout<<bestSz<<endl;
		}
	}

	clock_t endClk = clock();
	/*
	printf("#File=%s #K=%d #nodes=%d #nedges=%d\n",filename,k,orG.nbvtx,orG.nbedges);
	printf("#corennode=%d #corenedges=%d #peeltime=%.2f\n",coreG.nbvtx,coreG.nbedges,Utility::elapse_seconds(heuriClk, lvl1Clk));
	printf("#kernalnnode=%d #kernaldges=%d #strongredtime=%.2f\n",kernelG.nbvtx,kernelG.nbedges,Utility::elapse_seconds(lvl1Clk, lvl2Clk));
	printf("#heusol=%d #heutime=%.2f #bestSol=%d #totTime=%.2f\n",heuriSearcher.solSz,Utility::elapse_seconds(startClk,heuriClk),bestSz,Utility::elapse_seconds(startClk, endClk));
	*/
	printf("#File=%s\n#K=%d\n#nodes=%d\n#nedges=%d\n\n",filename,k,orG.nbvtx,orG.nbedges);
	printf("#corennode=%d\n#corenedges=%d\n#peeltime=%.2f\n\n",coreG.nbvtx,coreG.nbedges,Utility::elapse_seconds(heuriClk, lvl1Clk));
	printf("#kernalnnode=%d\n#kernaldges=%d\n#strongredtime=%.2f\n\n",kernelG.nbvtx,kernelG.nbedges,Utility::elapse_seconds(lvl1Clk, lvl2Clk));
	printf("#heusol=%d\n#heutime=%.2f\n#heusol2=%d\n#bestSol=%d\n#totTime=%.2f\n\n",heuriSearcher.solSz,Utility::elapse_seconds(startClk,heuriClk),heuriKernelSearcher.solSz, bestSz,Utility::elapse_seconds(startClk, endClk));
	printf("#optimal=%d\n#branches=%lld\n\n", optimal, branches);
	printf("#MaxSubG=%d\n\n", MaxSubG);
	//printf("#rule1=%d\n#rule2=%d\n#rule3=%d\n#rule4=%d\n#rule7=%d\n#rule8_0=%d\n#rule8=%d\n#rule9_0=%d\n#rule9_1=%d\n#rule9_2=%d\n#rule9=%d\n#rule11=%d\n#rule12=%d\n#rule1_1=%d\n#rule2_2=%d\n#rule3_3=%d\n#rule4_4=%d\n\n", rule1, rule2, rule3, rule4, rule7, rule8_0, rule8, rule9_0, rule9_1, rule9_2, rule9, rule11, rule12, rule1_1, rule2_2, rule3_3, rule4_4);


	sort(bestSol,bestSol+bestSz); for (int i = 0; i < bestSz; i++)printf("%d ", bestSol[i]); puts("");
	
	delete[] new2ori;
	delete[] bestSol;
	delete[] bestSolSub;
	delete[] core;
	delete[] dseq;
	delete[] dpos;
	delete[] dposSub;
	delete[] dseqSub;
	delete[] coreSub;
}

int main(int argc, char** argv) {
	printf("\n-----------------------------------------------------------------------------------------\n");
	if (argc >= 3) {
		strncpy(filename, argv[1], 1024);
		k = atoi(argv[2]);
		maxsec = atoi(argv[3]);
		KPX();
	}
	else printf("binary filename k\n");
	printf("-----------------------------------------------------------------------------------------\n\n\n\n\n");
}