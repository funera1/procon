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
#define VEC(type, c, n) std::vector<type> c(n);for(auto& i:c)std::cin>>i;
#define vec(type,n) vector<type>(n)
#define vvec(m,n) vector<vector<int>> (int(m),vector<int>(n))
#define ALL(a)  (a).begin(),(a).end()
#define pb push_back

using namespace std;
using ll = long long;
using Graph = vector<vector<int>>;
using P = pair<int,int>;


//bit全探索
vector<ll>bitSearch(int bit,int n){
    vector<ll>S;
    rep(i,n)if(bit&(1<<i))S.push_back(i);
    S.push_back(1e9);
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

        void merge(int x, int y){
            int rx = root(x);
            int ry = root(y);
            if(rx == ry)return;

            if(size(rx) < size(ry))swap(rx, ry);

            par[rx] += par[ry];
            par[ry] = rx;

            return;
        }

        bool same(int x, int y){
            return root(x) == root(y);
        }
};


//Combination MOD
const ll MOD = 1e9 + 7;
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
        fac_inv[i + 1] = fac_inv[i] * mpow(i + 1, MOD - 2) % MOD;
    }
}


// modint: mod 計算を int を扱うように扱える構造体
template<int MOD> struct Fp {
    long long val;
    constexpr Fp(long long v = 0) noexcept : val(v % MOD) {
        if (val < 0) val += MOD;
    }
    constexpr int getmod() { return MOD; }
    constexpr Fp operator - () const noexcept {
        return val ? MOD - val : 0;
    }
    constexpr Fp operator + (const Fp& r) const noexcept { return Fp(*this) += r; }
    constexpr Fp operator - (const Fp& r) const noexcept { return Fp(*this) -= r; }
    constexpr Fp operator * (const Fp& r) const noexcept { return Fp(*this) *= r; }
    constexpr Fp operator / (const Fp& r) const noexcept { return Fp(*this) /= r; }
    constexpr Fp& operator += (const Fp& r) noexcept {
        val += r.val;
        if (val >= MOD) val -= MOD;
        return *this;
    }
    constexpr Fp& operator -= (const Fp& r) noexcept {
        val -= r.val;
        if (val < 0) val += MOD;
        return *this;
    }
    constexpr Fp& operator *= (const Fp& r) noexcept {
        val = val * r.val % MOD;
        return *this;
    }
    constexpr Fp& operator /= (const Fp& r) noexcept {
        long long a = r.val, b = MOD, u = 1, v = 0;
        while (b) {
            long long t = a / b;
            a -= t * b; swap(a, b);
            u -= t * v; swap(u, v);
        }
        val = val * u % MOD;
        if (val < 0) val += MOD;
        return *this;
    }
    constexpr bool operator == (const Fp& r) const noexcept {
        return this->val == r.val;
    }
    constexpr bool operator != (const Fp& r) const noexcept {
        return this->val != r.val;
    }
    friend constexpr ostream& operator << (ostream &os, const Fp<MOD>& x) noexcept {
        return os << x.val;
    }
    friend constexpr Fp<MOD> modpow(const Fp<MOD> &a, long long n) noexcept {
        if (n == 0) return 1;
        auto t = modpow(a, n / 2);
        t = t * t;
        if (n & 1) t = t * a;
        return t;
    }
};
using mint = Fp<1000000007>;

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


//素数判定
bool isPrime(int x){
    int i;
    if(x < 2)return 0;
    else if(x == 2) return 1;
    if(x%2 == 0) return 0;
    for(i = 3; i*i <= x; i += 2) if(x%i == 0) return 0;
    return 1;
}

//桁和
int digsum(int n) {
    int res = 0;
    while(n > 0) {
        res += n%10;
        n /= 10;
    }
    return res;
}


//約数全列挙
vector<int> enum_div(int n){
    vector<int> ret;
    for(int i = 1 ; i*i <= n ; ++i){
        if(n%i == 0){
            ret.push_back(i);
            if(i != 1 && i*i != n){
                ret.push_back(n/i);
            }
        }
    }
    return ret;
}

//Segment木
/*RMQ : [0, n-1]について、区間ごとの最小値を管理する構造体
  update(i, x) : i番目の要素をxに更新.O(log(n))
  query(a, b) : [a, b)での最小の要素を取得.O(log(n))
*/

template<typename T>
struct RMQ{
    const T INF = numeric_limits<T>::max();
    int n;            //葉の数
    vector<T> dat;    //完全二分木の配列
    RMQ(int n_) : n(), dat(n_ * 4, INF){    //葉の数は2^xの形
        int x = 1;
        while(n_ > x){
            x *= 2;
        }
        n = x;
    }

    void update(int i, T x){
        i += n - 1;
        dat[i] = x;
        while(i > 0){
            i = (i - 1) / 2;    //parent
            dat[i] = min(dat[i + 2 + 1], dat[i * 2 + 2]);
        }
    }

    //the minimum elsemnt of[a, b)
    T query(int a, int b){return qurey_sub(a, b, 0, 0, n);}
    T query_sub(int a, int b, int k, int l, int r){
        if(r <= a || b <= l){
            return INF;
        }
        else if(a <= l && r <= b){
            return dat[k];
        }
        else {
            T vl = query_sub(a, b, k * 2 + 1, l, (l + r) / 2);
            T vr = query_sub(a, b, k * 2 + 2, (l + r) / 2, r);
            return min(vl, vr);
        }
    }
};

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
    int lower_bound(T w){
        if(w <= 0)return 0;
        else {
            int x = 0, r = 1;
            while(r < n)r = r << 1;
            for(int len = r; len > 0; len = len >> 1){
                w -= bit[x + len];
                x += len;
            }
            return x + 1;
        }
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
struct edge{int to, cost;};
vector<ll>  dijkstra(int s, vector<vector<edge>> G, int V){
    vector<ll> d(V, INF);
    priority_queue<P, vector<P>, greater<P>>pq;
    d[s] = 0;
    pq.push(P(0, s));

    while(!pq.empty()){
        P p = pq.top();
        pq.pop();
        int v = p.second;
        if(d[v] < p.first)continue;
        int sz = G[v].size();
        for(int i = 0; i < sz; i++){
            edge e = G[v][i];
            if(d[e.to] > d[v]+e.cost){
                d[e.to] = d[v] + e.cost;
                pq.push(P(d[e.to], e.to));
            }
        }
    }
    return d;
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

    X query(int a, int b, int k = 0, int l = 0, int r = -1){
        if(r < 0)r = n;
        if(r <= a || b <= l)return ex;
        if(a <= l && r <= b)return dat[k];

        X vl = query(a, b, k * 2 + 1, l, (l + r) / 2);
        X vr = query(a, b, k * 2 + 2, (l + r) / 2, r);
        return fx(vl, vr);
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

//prim法
struct edge{
    int to;
    ll cost;
};

ll prim(vector<vector<ll>> Graph, int V){
    ll res = 0;
    vector<bool> used(V, false);
    priority_queue<P, vector<P>, greater<P>> pq;
    pq.push(0, 0);
    while(!pq.empty()){
        P p = pq.top();
        pq.pop();
        if(used[p.second])continue;
        used[p.second] = true;
        res += p.first;
        for(auto e : Graph[p.second]){
            if(!used[e.to])pq.push(P(e.cost, e.to));
        }
    }
    return res;
}

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

