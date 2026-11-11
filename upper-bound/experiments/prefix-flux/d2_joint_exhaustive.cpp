// Independent integer exhaustive audit of a fixed two-round instance.
// Input: n m M, then m rows of each of the two row permutations.
// Enumerates every input-height vector in [0,m]^n with sum M.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

struct Audit {
    int n,m,M; std::vector<int> p1,p2,mid,h,best_h;
    std::uint64_t leaves=0; long long best=-1;
    void visit(int u,int left) {
        if(u==n) {
            if(left!=0) return;
            ++leaves;
            std::vector<int> f(n,0);
            for(int v=0;v<n;++v)
                for(int r=0;r<mid[v];++r) ++f[p2[r*n+v]];
            long long score=0;
            for(int v=0;v<n;++v) score+=std::max(0,n*f[v]-M);
            if(score>best) {best=score;best_h=h;}
            return;
        }
        int lo=std::max(0,left-(n-u-1)*m),hi=std::min(m,left);
        if(lo>hi) return;
        for(int r=0;r<lo;++r) ++mid[p1[r*n+u]];
        for(int height=lo;height<=hi;++height) {
            h[u]=height;visit(u+1,left-height);
            if(height<hi) ++mid[p1[height*n+u]];
        }
        for(int r=0;r<hi;++r) --mid[p1[r*n+u]];
    }
    void run(std::istream& in,std::ostream& out) {
        if(!(in>>n>>m>>M) || n<1 || n>16 || m<1 || m>16 || M<0 || M>n*m)
            throw std::runtime_error("unsupported dimensions");
        for(auto* p:{&p1,&p2}) {
            p->resize(n*m);
            for(int r=0;r<m;++r) {
                std::vector<int> row(n);
                for(int u=0;u<n;++u) {
                    if(!(in>>row[u])) throw std::runtime_error("missing permutation");
                    (*p)[r*n+u]=row[u];
                }
                std::sort(row.begin(),row.end());
                for(int u=0;u<n;++u) if(row[u]!=u) throw std::runtime_error("invalid permutation");
            }
        }
        // Independent coefficient count; cap before allowing expensive enumeration.
        const std::uint64_t cap=200000001;
        std::vector<std::uint64_t> count(M+1,0);count[0]=1;
        for(int u=0;u<n;++u) {
            std::vector<std::uint64_t> next(M+1,0);
            for(int s=0;s<=M;++s) for(int x=0;x<=m && s+x<=M;++x)
                next[s+x]=std::min(cap,next[s+x]+count[s]);
            count=next;
        }
        if(count[M]>=cap) throw std::runtime_error("more than 200 million profiles");
        mid.assign(n,0);h.assign(n,0);visit(0,M);
        if(leaves!=count[M]) throw std::runtime_error("enumeration count mismatch");
        for(int x:mid) if(x!=0) throw std::runtime_error("restore mismatch");
        out<<"{\"profiles\":"<<leaves<<",\"maximum_numerator\":"<<best
           <<",\"denominator\":"<<n*n<<",\"input\":[";
        for(int u=0;u<n;++u) out<<(u?",":"")<<best_h[u];
        out<<"]}\n";
    }
};
int main(int argc,char** argv) {
    try {
        if(argc!=3) throw std::runtime_error("usage: audit instance.txt output.json");
        std::ifstream in(argv[1]);std::ofstream out(argv[2]);
        if(!in || !out) throw std::runtime_error("cannot open files");
        Audit audit;audit.run(in,out);
    } catch(const std::exception& e) {std::cerr<<e.what()<<"\n";return 1;}
}
