#include<iostream>
#include<stdio.h>
//#include <bits/stdc++.h>
#include<vector>
#include<float.h>
#include<iomanip>
#include<algorithm>
#include<string>
#include<cstring>
#include<math.h>
#include<cmath>
#include<sstream>
#include<set>
#include<map>
#include<queue>
#include <cassert>
#include <cmath>
#include<cstdint>
#define INF 1e9
#define rep(i,n)for(long long i=0;(i)<(long long)(n);i++)
#define REP(i,a,b)for(long long i=(long long)(a);(i)<=(long long)(b);i++)
#define ALL(a)  (a).begin(),(a).end()
#define pb push_back
#define fi first
#define se second
#define sz(x) ((int)x.size())

using namespace std;
using ll = long long int;
using ld = long double;
using P = pair<ll, ll>;

const ll ZER = 0;
const ll MOD = 1e9 + 7;


//bit全探索
vector<ll>bitSearch(int bit,int n){
    vector<ll>S;
    rep(i,n)if(bit&(1<<i))S.push_back(i);
    // S.push_back(1e9);
    return S;
}


//最大公約数
ll gcd(ll a, ll b){
    if(a % b == 0)return b;
    else return gcd(b, a % b);
}



//コンビネーション(パスカルの三角形)
ll COMB(int n, int r) {
  std::vector<std::vector<long long>> v(n + 1,std::vector<long long>(n + 1, 0));
  for (int i = 0; i < v.size(); i++) {
    v[i][0] = 1;
    v[i][i] = 1;
  }
  for (int j = 1; j < v.size(); j++) {
    for (int k = 1; k < j; k++) {
      v[j][k] = (v[j - 1][k - 1] + v[j - 1][k]);
    }
  }
  return v[n][r];
}


//エラトステネスの篩
vector<bool> IsPrime;

void sieve(size_t max){
    if(max+1 > IsPrime.size()){     // resizeで要素数が減らないように
        IsPrime.resize(max+1,true); // IsPrimeに必要な要素数を確保
    } 
    IsPrime[0] = false; // 0は素数ではない
    IsPrime[1] = false; // 1は素数ではない

    for(size_t i=2; i*i<=max; ++i) // 0からsqrt(max)まで調べる
        if(IsPrime[i]) // iが素数ならば
            for(size_t j=2; i*j<=max; ++j) // (max以下の)iの倍数は
                IsPrime[i*j] = false;      // 素数ではない
}

//vectorの重複取り除く
template <typename T>
void vectorErase(vector<T> a){
    sort(ALL(a));
    a.erase(unique(ALL(a)), a.end());
}


// UnionFind木(サイズ持ち)
class UnionFind {
    public : 

        vector<int> par;

        UnionFind(int N){
            par = vector<int>(N, -1);
        }

        int parent(int x){
            return par[x];
        }

        int root(int x){
            if(par[x] < 0)return x;
            return par[x] = root(par[x]);
        }

        int size(int x){
            return -par[root(x)];
        }

        bool merge(int x, int y){
            int rx = root(x);
            int ry = root(y);
            if(rx == ry)return false;

            if(size(rx) < size(ry))swap(rx, ry);

            par[rx] += par[ry];
            par[ry] = rx;

            return true;
        }

        bool same(int x, int y){
            return root(x) == root(y);
        }
};


//Combination MOD
vector<ll> fac(SMX);
vector<ll> fac_inv(SMX);

ll mpow(ll x, ll n, ll MOD = 1e9 + 7){
    if(n < 0)return 0;
    ll ans = 1;
    while(n != 0){
        if(n & 1)ans = ans * x % MOD;
        x = x * x % MOD;
        n = n >> 1;
    }
    return ans;
}

ll comb(ll a, ll b){
    if(a == 0 && b == 0)return 1;
    if(a < b || a < 0 || b < 0)return 0;

    ll tmp = fac_inv[a - b] * fac_inv[b] % MOD;
    return tmp * fac[a] % MOD;
}

void preComb(){
    fac[0] = 1;
    fac_inv[0] = 1;
    for(ll i = 0; i < SMX; i++){
        fac[i + 1] = fac[i] * (i + 1) % MOD;
        fac_inv[i + 1] = fac_inv[i] * mpow(i + 1, MOD - 2, MOD) % MOD;
    }
}


// 多倍長テンプレ
/* ---------------------- ここから ---------------------- */
#include <boost/multiprecision/cpp_dec_float.hpp>
#include <boost/multiprecision/cpp_int.hpp>
namespace mp = boost::multiprecision;
// 任意長整数型
using Bint = mp::cpp_int;
// 仮数部が1024ビットの浮動小数点数型(TLEしたら小さくする)
using Real = mp::number<mp::cpp_dec_float<1024>>;
/* ---------------------- ここまで ---------------------- */


//桁dp
ll dp[32][2][4];
ll solve(string s){
    //fill(dp,(ll)0);
    dp[0][0][0] = 1;
    //string s = to_string(n);
    rep(i,s.size()){            //各桁について調べる
        const int D = s[i]-'0';
        rep(j,2){               //その桁がもとの数字の桁の数と一致してるかどうか
            rep(k,4){           //そのdpが4か9をもつかどうか
                rep(d,(j?10:D+1)){
                    if(d == 0)dp[i + 1][j || (d < D)][k] += dp[i][j][k];
                    if(k == 3)continue;
                    if(d != 0)dp[i + 1][j || (d < D)][k + 1] += dp[i][j][k];
                }
            }
        }
    }
    return dp[s.size()][0][];
}


//BIT
template <typename T>
struct BIT{
    int n;  //配列の要素数
    vector<T> bit;  //データの格納先
    BIT(int n_) : n(n_ + 1), bit(n, 0){}

    void add(int i, T x){
        for(int idx = i; idx < n; idx += (idx & -idx)){
            bit[idx] += x;
        }
    }

    T sum(int i){
        T s(0);
        for(int idx = i; idx > 0; idx -= (idx & -idx)){
            s += bit[idx];
        }
        return s;
    }

    //sum(a_i) >= w となるような最小のxを求める
    int lower_bound(T w) { // a_1 + a_2 + ... + a_x >= w となるような最小の x を求める(ただし a_i >= 0)
    if (w <= 0) return 0;
    else {
        int x = 0, r = 1;
        while (r < n) r = r << 1;
            for (int len = r; len > 0; len = len >> 1) { // 長さlenは1段下るごとに半分に
                if (x + len < n && bit[x + len] < w) { // 採用するとき
                    w -= bit[x + len];
                    x += len;
                }
            }
            return x + 1;
        }
    }
    

    T num(int i){
        T res = sum(i);
        if(i != 1)res -= sum(i - 1);
        return res;
    }
};



//区間和対応BIT
template <typename T>
struct segBIT {
    int n;             // 要素数
    vector<T> bit[2];  // データの格納先
    segBIT(int n_) { init(n_); }
    void init(int n_) {
        n = n_ + 1;
        for (int p = 0; p < 2; p++) bit[p].assign(n, 0);
    }
    void add_sub(int p, int i, T x) {
        for (int idx = i; idx < n; idx += (idx & -idx)) {
            bit[p][idx] += x;
        }
    }
    void add(int l, int r, T x) {  // [l,r) に加算
        add_sub(0, l, -x * (l - 1));
        add_sub(0, r, x * (r - 1));
        add_sub(1, l, x);
        add_sub(1, r, -x);
    }
    T sum_sub(int p, int i) {
        T s(0);
        for (int idx = i; idx > 0; idx -= (idx & -idx)) {
            s += bit[p][idx];
        }
        return s;
    }
    T sum(int i) { return sum_sub(0, i) + sum_sub(1, i) * i; }
};


//dijkstra法
//P(to, cost)
vector<ll>  dijkstra(int s, vector<vector<P>> G, int V){
    vector<ll> d(V, INF);
    priority_queue<P, vector<P>, greater<P>>pq;
    d[s] = 0;
    pq.push(P(0, s));

    while(!pq.empty()){
        P p = pq.top();
        pq.pop();
        int v = p.second;
        if(d[v] < p.first)continue;
        int siz = G[v].size();
        for(int i = 0; i < siz; i++){
            P e = G[v][i];
            if(d[e.fi] > d[v] + e.se){
                d[e.fi] = d[v] + e.se;
                pq.push(P(d[e.fi], e.fi));
            }
        }
    }
    return d;
}

//bellman-ford
struct edge{
    int from, to;
    ll cost;
};

//始点から到達可能でかつ終点へ到達可能な不閉路が検出されたらfalse、そうでないならtrue
bool bellman_ford(int n, const vector<edge> &es, vector<ll> &cost, int s, int g){
    const ll inf = 1e18;
    cost.assign(v, inf);
    cost[s] = 0;

    rep(i, n * 2){
        for(auto &e : es){
            if(cost[e.from] < inf && cost[e.from] + e.cost < cost[e.to]){
                if(i >= n - 1 && e.to == g)return false;
                else if(i >= n - 1)cost[e.to] = -inf;
                else cost[e.to] = cost[e.from] + e.cost;;
            }
        }
    }
    return true;
}

//頂点u, vを含む最小木
bool isgoal = false;
int goal;
deque<int> deq;
void dfs(int v, int par){
    if(isgoal)return;
    deq.push_back(v);

    if(v == goal){isgoal = true;return;};
    for(auto nv : G[v]){
        if(nv == par)continue;
        dfs(nv, v);
    }

    if(isgoal)return;
     deq.pop_back();
}


//桁dp
ll dp[32][2][2];
ll solve(ll n){
    Fill(dp,(ll)0);
    dp[0][0][0] = 1;
    string s = to_string(n);
    rep(i,s.size()){            //各桁について調べる
        const int D = s[i]-'0';
        rep(j,2){               //その桁がもとの数字の桁の数と一致してるかどうか
            rep(k,2){           //そのdpが4か9をもつかどうか
                rep(d,(j?10:D+1)){
                    dp[i+1][j || (d<D)][k || d==4 || d==9] += dp[i][j][k];
                }
            }
        }
    }
    return dp[s.size()][0][1]+dp[s.size()][1][1];
}

//Osa_k法
vector<ll> sieve(ll n){
    vector<ll> res(n);
    iota(ALL(res), 0);
    for(int i = 2; i * i < n; i++){
        if(res[i] < i)continue;
        for(int j = i * i; j < n; j += i){
            if(res[j] == j)res[j] = i;
        }
    }
    return res;
}

vector<ll> factor(ll n, const vector<ll> & min_factor){
    //min_factorはsieve()で得られたもの
    vector<ll> res;
    while(n > 1){
        res.push_back(min_factor[n]);
        n /= min_factor[n];
    }
    return res;
}

/* SegTree<X>(n,fx,ex): モノイド(集合X, 二項演算fx, 単位元ex)についてサイズnで構築
    set(int i, X x), build(): i番目の要素をxにセット。まとめてセグ木を構築する。O(n)
    update(i,x): i 番目の要素を x に更新。O(log(n))
    query(a,b): [a,b) 全てにfxを作用させた値を取得。O(log(n))
*/

//抽象化したセグ木 SegTree<集合の型>(集合のサイズ,演算,単位元)
template <typename X>
struct SegTree{
    using FX = function<X(X, X)>;   //X*X -> X となる関数の型
    int n;
    FX fx;
    const X ex;
    vector<X> dat;
    SegTree(int n_, FX fx_, X ex_) : n(), fx(fx_), ex(ex_), dat(n_ * 4, ex_) {
        int x = 1;
        while(n_ > x)x *= 2;
        n = x;
    }
    void set(int i, X x){
        dat[i + n - 1] = x;
    }

    void build() {
        for(int k = n - 2; k >= 0; k--)dat[k] = fx(dat[2 * k + 1], dat[2 * k + 2]);
    }

    void update(int i, X x){
        i += n - 1;
        dat[i] = x;
        while(i > 0){
            i = (i - 1) / 2;
            dat[i] = fx(dat[i * 2 + 1], dat[i * 2 + 2]);
        }
    }

    X get(int a, int b, int k = 0, int l = 0, int r = -1){
        if(r < 0)r = n;
        if(r <= a || b <= l)return ex;
        if(a <= l && r <= b)return dat[k];

        X vl = get(a, b, k * 2 + 1, l, (l + r) / 2);
        X vr = get(a, b, k * 2 + 2, (l + r) / 2, r);
        return fx(vl, vr);
    }

    X num(int i){
        return dat[i + n - 1];
    }
};


/* SegTreeLazy<X,M>(n,fx,fa,fm,ex,em): モノイド(集合X, 二項演算fx,fa,fm, 単位元ex,em)についてサイズnで構築
    set(int i, X x), build(): i番目の要素をxにセット。まとめてセグ木を構築する。O(n)
    update(i,x): i 番目の要素を x に更新。O(log(n))
    query(a,b):  [a,b) 全てにfxを作用させた値を取得。O(log(n))
*/
template <typename X, typename M>
struct SegTreeLazy {
    using FX = function<X(X, X)>;
    using FA = function<X(X, M)>;
    using FM = function<M(M, M)>;
    int n;
    FX fx;
    FA fa;
    FM fm;
    const X ex;
    const M em;
    vector<X> dat;
    vector<M> lazy;
    SegTreeLazy(int n_, FX fx_, FA fa_, FM fm_, X ex_, M em_)
        : n(), fx(fx_), fa(fa_), fm(fm_), ex(ex_), em(em_), dat(n_ * 4, ex), lazy(n_ * 4, em) {
        int x = 1;
        while (n_ > x) x *= 2;
        n = x;
    }
    void set(int i, X x) { dat[i + n - 1] = x; }
    void build() {
        for (int k = n - 2; k >= 0; k--) dat[k] = fx(dat[2 * k + 1], dat[2 * k + 2]);
    }
    /* lazy eval */
    void eval(int k) {
        if (lazy[k] == em) return;  // 更新するものが無ければ終了
        if (k < n - 1) {            // 葉でなければ子に伝搬
            lazy[k * 2 + 1] = fm(lazy[k * 2 + 1], lazy[k]);
            lazy[k * 2 + 2] = fm(lazy[k * 2 + 2], lazy[k]);;
        }
        // 自身を更新
        dat[k] = fa(dat[k], lazy[k]);
        lazy[k] = em;
    }
    void update(int a, int b, M x, int k = 0, int l = 0, int r = -1) {
        if(r == -1)r = n;
        eval(k);
        if (a <= l && r <= b) {  // 完全に内側の時
            lazy[k] = fm(lazy[k], x);
            eval(k);
        } else if (a < r && l < b) {                     // 一部区間が被る時
            update(a, b, x, k * 2 + 1, l, (l + r) / 2);  // 左の子
            update(a, b, x, k * 2 + 2, (l + r) / 2, r);  // 右の子
            dat[k] = fx(dat[k * 2 + 1], dat[k * 2 + 2]);
        }
    }
    X get(int a, int b, int k = 0, int l = 0, int r = -1) {
        if(r == -1)r = n;
        eval(k);
        if (r <= a || b <= l) {  // 完全に外側の時
            return ex;
        } else if (a <= l && r <= b) {  // 完全に内側の時
            return dat[k];
        } else {  // 一部区間が被る時
            X vl = get(a, b, k * 2 + 1, l, (l + r) / 2);
            X vr = get(a, b, k * 2 + 2, (l + r) / 2, r);
            return fx(vl, vr);
        }
    }
};

/* 小数点n以下で四捨五入する */
double round_n(double number, double n)
{
    number = number * pow(10,n-1); //四捨五入したい値を10の(n-1)乗倍する。
    number = round(number); //小数点以下を四捨五入する。
    number /= pow(10, n-1); //10の(n-1)乗で割る。
    return number;
}


/* Prim(隣接行列) : プリム法で minimum spanning tree を求める構造体
    入力: 隣接行列でのグラフ G
    最小全域木の重みの総和: sum
    計算量: O(|V|^2)
*/
template <typename T>
struct Prim {
    T sum;              // MSTの重みの総和
    int n;                // 頂点数
    vector<T> mincost;  // 既に確定した頂点からの最小コスト（確定済みから行けない時は INF）
    vector<bool> used;    // 既に確定したかどうか
    Prim(vector<vector<T>> const& Graph) {
        init(Graph);
    }
    void init(vector<vector<T>> const& Graph) {
        n = (int)Graph.size();
        mincost.assign(n, INF);
        used.assign(n, false);
        sum = 0;
        mincost[0] = 0;  // 始め頂点0からスタートさせる
        while (true) {
            int v = -1;
            for (int u = 0; u < n; u++) {  // コストが最小で行ける頂点 v を探す
                if (!used[u] && (v == -1 || mincost[u] < mincost[v])) v = u;
            }
            if (v == -1) break;  // MST ができたので終了
            used[v] = true;
            sum += mincost[v];
            for (int u = 0; u < n; u++) {  // 確定した頂点から行ける頂点について、最小コストを更新
                if (Graph[v][u] != -1) mincost[u] = min(mincost[u], Graph[v][u]);
            }
        }
    }
};

/* prim(隣接グラフ)
   入力: 隣接グラフ G
   計算量 O(|E| log |V|)
   引数: prim(グラフ, 頂点数)
*/
ll prim(vector<P> G, int V){
    vector<bool> seen(n, false);
    priority_queue<P, vector<P>, greater<P>> pq;
    pq.push(P(0, 0));
    ll ret = 0;
    while(!pq.empty()){
        auto [cost, v] = pq.top;
        pq.pop(;
        if(seen[v]))continue;
        seen[v] = true;
        ret += cost;
        for(auto nv : G[v]){
            pq.push(nv);
        }
    }
    return ret;
}



//Kruskal法------------------------------------------------------------------------------
/* 
    isSame(x, y): x と y が同じ集合にいるか。 計算量はならし O(α(n))
    unite(x, y): x と y を同じ集合にする。計算量はならし O(α(n))
*/
struct UnionFind {  // The range of node number is u 0 v n-1
    vector<int> rank, parents;
    UnionFind() {}
    UnionFind(int n) {  // make n trees.
        rank.resize(n, 0);
        parents.resize(n, 0);
        for (int i = 0; i < n; i++) {
            makeTree(i);
        }
    }
    void makeTree(int x) {
        parents[x] = x;  // the parent of x is x
        rank[x] = 0;
    }
    bool isSame(int x, int y) { return findRoot(x) == findRoot(y); }
    void unite(int x, int y) {
        x = findRoot(x);
        y = findRoot(y);
        if (rank[x] > rank[y]) {
            parents[y] = x;
        } else {
            parents[x] = y;
            if (rank[x] == rank[y]) {
                rank[y]++;
            }
        }
    }
    int findRoot(int x) {
        if (x != parents[x]) parents[x] = findRoot(parents[x]);
        return parents[x];
    }
};
// 辺の定義
struct Edge {
    long long u;
    long long v;
    long long cost;
};
bool comp_e(const Edge &e1, const Edge &e2) { return e1.cost < e2.cost; } // 辺を直接比較するための関数
/* Kruskal :クラスカル法で minimum spanning tree を求める構造体
    入力: 辺のvector, 頂点数V
    最小全域木の重みの総和: sum
    計算量: O(|E|log|V|)
*/
struct Kruskal {
    UnionFind uft;
    long long sum;  // 最小全域木の重みの総和
    vector<Edge> edges;
    int V;
    Kruskal(const vector<Edge> &edges_, int V_) : edges(edges_), V(V_) { init(); }
    void init() {
        sort(edges.begin(), edges.end(), comp_e); // 辺の重みでソート
        uft = UnionFind(V);
        sum = 0;
        for (auto e : edges) {
            if (!uft.isSame(e.u, e.v)) { // 閉路にならなければ加える
                uft.unite(e.u, e.v);
                sum += e.cost;
            }
        }
    }
};
//------------------------------------------------------------------------------

// ローリングハッシュ
//LCPを二分探索で求める機能付き
struct RollingHash {
    static const int base1 = 1007, base2 = 2009;
    static const int mod1 = 1000000007, mod2 = 1000000009;
    vector<long long> hash1, hash2, power1, power2;

    // construct
    RollingHash(const string &S) {
        int n = (int)S.size();
        hash1.assign(n+1, 0);
        hash2.assign(n+1, 0);
        power1.assign(n+1, 1);
        power2.assign(n+1, 1);
        for (int i = 0; i < n; ++i) {
            hash1[i+1] = (hash1[i] * base1 + S[i]) % mod1;
            hash2[i+1] = (hash2[i] * base2 + S[i]) % mod2;
            power1[i+1] = (power1[i] * base1) % mod1;
            power2[i+1] = (power2[i] * base2) % mod2;
        }
    }
    
    // get hash of S[left:right]
    inline pair<long long, long long> get(int l, int r) const {
        long long res1 = hash1[r] - hash1[l] * power1[r-l] % mod1;
        if (res1 < 0) res1 += mod1;
        long long res2 = hash2[r] - hash2[l] * power2[r-l] % mod2;
        if (res2 < 0) res2 += mod2;
        return {res1, res2};
    }

    // get lcp of S[a:] and T[b:]
    inline int getLCP(int a, int b) const {
        int len = min((int)hash1.size() - a, (int)hash1.size() - b);
        int low = 0, high = len;
        while(high - low > 1){
            int mid = (low + high) >> 1;
            if(get(a, a + mid) != get(b, b + mid))high = mid;
            else low = mid;
        }
        return low;
    }
};

//トポロジカルソート
//topo_sort
vector<int> topo_sort(const Graph &G){
    vector<int> res;
    int n = (int)G.size();
    vector<int> ind(n);  //ind[i]: 頂点iの入次数
    //次数を数えておく
    rep(i, n){
        for(auto e : G[i]){
            ind[e]++;
        }
    }
    queue<int> que;
    rep(i, n){
        if(ind[i] == 0)que.push(i);
    }
    //bfs
    while(!que.empty()){
        int v = que.front();
        res.pb(v);
        que.pop();
        for(auto nv : G[v]){
            ind[nv]--;
            if(ind[nv] == 0){
                que.push(nv);
            }
        }
    }
    return res;
}

//LCA
template <typename T>
struct LCA{
    vector<vector<int>> par;  //par[k][u]:= uの2^k先の点
    vector<T> dist; //rootからの距離
    LCA(const Graph &G, int root = 0){
        init(G, root);
    }

    //初期化
    void init (const Graph &G, int root = 0){
        int V = G.size();
        int K = 1;
        while((1 << K) < V)K++;
        parent.assign(K, vector<int>(V, -1));
        dist.assign(V, -1);
        dfs(G, root, -1, 0);
        rep(k, K - 1){
            rep(v, V){
                if(par[k][v] < 0){
                    par[k + 1][v] = -1;
                }
                else{
                    par[k + 1][v] = par[k][par[k][v]];
                }
            }
        }
    }

    //根からの距離と1つ先の頂点を求める
    void dfs(const Graph &G, int v, int p, int d){
        par[0][v] = p;
        dist[v] = d;
        for(auto nv : G[v]){
            if(nv != p)dfs(G, nv, v, d + 1);
        }
    }

    //(u, v)のLCAを求める
    int query(int u, int v){
        if(dist[u] < dist[v])swqp(u, v);
        int K = par.size();
        //LCAまでの距離を同じにする
        rep(k, K){
            if((dist[u] - dist[v]) >> k & 1)u = par[k][u];
        }

        //二分探索
        if(u == v)return u;
        for(int k = K - 1; k >= 0; k--){
            if(par[k][u] != par[k][v]){
                u = par[k][u];
                v = par[k][v];
            }
        }
        return par[0][u];
    }

    //2頂点間の距離:O(log N)
    T get_dist(int u, int v) { 
        return dist[u] + dist[v] - 2 * dist[query(u, v)];
    }

    //2頂点上に点aがあるか
    bool is_on_path(int u, int v, int a) { 
        return get_dist(u, a) + get_dist(a, v) == get_dist(u, v);
    }
};

//最小包含円
template <class iter>
std::pair<P, ld> min_ball(iter left, iter right, int seed = 1333) {
    const int n = right - left;

    assert(n >= 1);
    if (n == 1) {
        return {*left, ld(0)};
    }

    std::mt19937 mt(seed);
    std::shuffle(left, right, mt);
    // std::random_shuffle(left, right); // simple but deprecated

    iter ps = left;
    using circle = std::pair<P, ld>;

    auto make_circle_3 = [](const P &a, const P &b, const P &c) -> circle {
        ld A = std::norm(b - c), B = std::norm(c - a), C = std::norm(a - b),
           S = cross(b - a, c - a);
        P p = (A * (B + C - A) * a + B * (C + A - B) * b + C * (A + B - C) * c) / (4 * S * S);
        ld r2 = std::norm(p - a);
        return {p, r2};
    };

    auto make_circle_2 = [](const P &a, const P &b) -> circle {
        P c = (a + b) / (ld)2;
        ld r2 = std::norm(a - c);
        return {c, r2};
    };

    auto in_circle = [](const P &a, const circle &c) -> bool {
        return std::norm(a - c.first) <= c.second + eps;
    };

    circle c = make_circle_2(ps[0], ps[1]);

    // MiniDisc
    for (int i = 2; i < n; ++i) {
        if (!in_circle(ps[i], c)) {
            // MiniDiscWithPoint
            c = make_circle_2(ps[0], ps[i]);
            for (int j = 1; j < i; ++j) {
                if (!in_circle(ps[j], c)) {
                    // MiniDiscWith2Points
                    c = make_circle_2(ps[i], ps[j]);
                    for (int k = 0; k < j; ++k) {
                        if (!in_circle(ps[k], c)) {
                            c = make_circle_3(ps[i], ps[j], ps[k]);
                        }
                    }
                }
            }
        }
    }
    return c;
}


//拡張ユークリッド
//extgcd(a, b, x, y): a*x+b*y = gcd(a, b)を満たすx, yが格納される。return gcd(a, b)
ll extgcd(ll a, ll b, ll &x, ll &y){
    ll g = a;
    x = 1;
    y = 0;
    if(b != 0){
        g = extgcd(b, a % b, y, x);
        y -= (a / b) * x;
    }
    return g;
}

//逆元
//mod_inverse(a, b): a^-1 (mod m)
ll mod_inverse(ll a, ll m){
    ll x, y;
    extgcd(a, m, x, y);
    return (m + x % m) % m;
}


//scc
//強連結成分分解
struct scc_graph {
    int V;                          //頂点数
    vector<vector<int>> G;          //グラフの隣接リスト
    vector<vector<int>> rG;         //逆辺を張ったグラフ
    vector<int> vs;                 //帰りがけの並び
    vector<bool> used;              //すでに調べたか
    vector<int> cmp;                //属する強連結成分のトポロジカル順序

    scc_graph(int V_) : V(), G(V_ + 1), rG(V_ + 1), used(V_ + 1), cmp(V_ + 1) {}


    //辺を追加
    void add_edge(int from, int to){
        assert(0 <= from && from < V);
        assert(0 <= to && to < V);
        G[from].push_back(to);
        rG[to].push_back(from);
    }
    
    //1回目のdfs
    void dfs(int v){
        used[v] = true;
        assert(0 <= v && v < V);
        for (int i = 0; i < G[v].size(); i++) {
            if(!used[G[v][i]]) dfs(G[v][i]);
        }
        vs.push_back(v);
    }

    //2回目のdfs
    void rdfs(int v, int k){
        assert(0 <= v && v < V);
        used[v] = true;
        cmp[v] = k;
        for(int i = 0; i < rG[v].size(); i++){
            if(!used[rG[v][i]]) rdfs(rG[v][i], k);
        }
    }

    //scc: O(V + E)
    int scc(){
        used = vector<bool> (V, false);
        vs.clear();
        for(int v = 0; v < V; v++){
            if(!used[v]) dfs(v);
        }
        used = vector<bool> (V, false);
        int k = 0;
        for(int i = vs.size() - 1; i >= 0; i--){
            if(!used[vs[i]]) rdfs(vs[i], k++);
        }
        return k;
    }
};
