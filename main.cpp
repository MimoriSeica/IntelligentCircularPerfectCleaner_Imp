#include <iostream>
#include <string>
#include <vector>
#include <deque>
#include <queue>
#include <algorithm>
#include <iomanip>
#include <set>
#include <map>
#include <bitset>
#include <cmath>
#include <complex>
#include <array>
#include <functional>

using namespace std;

#define REP(i,n) for(ll (i) = (0);(i) < (n);++i)
#define REV(i,n) for(ll (i) = (n) - 1;(i) >= 0;--i)
#define PB push_back
#define EB emplace_back
#define MP make_pair
#define FI first
#define SE second
#define SHOW1d(v,n) {REP(WW,n)cerr << v[WW] << ' ';cerr << endl << endl;}
#define SHOW2d(v,WW,HH) {REP(W_,WW){REP(H_,HH)cerr << v[W_][H_] << ' ';cerr << endl;}cerr << endl;}
#define ALL(v) v.begin(),v.end()
#define Decimal fixed<<setprecision(20)
#define INF 1000000000
#define LLINF 1000000000000000000LL
#define MOD 998244353

typedef long long ll;
typedef pair<ll,ll> P;
//--------geometry original ------------------
#define curr(PP, i) PP[i]
#define next(PP, i) PP[(i+1)%PP.size()]
#define diff(PP, i) (next(PP, i) - curr(PP, i))
#define eq(n,m) (abs((n)-(m)) < EPS)

typedef long long ll;
typedef pair<ll, ll> P;

const double EPS = 1e-8;
const double EPS_GIG = 1e-3;
const double PI = acos(-1.0);
typedef complex<double> point;
namespace std {
	bool operator < (const point& a, const point& b) {
		return real(a) != real(b) ? real(a) < real(b) : imag(a) < imag(b);
	}

	bool operator == (const point& a,const point& b) {
		return (abs(a.real() - b.real()) < EPS && abs(a.imag() - b.imag()) < EPS);
	}
}
struct circle {
	point p; double r;
	circle(){}
	circle(const point &p, double r) : p(p), r(r) { }
};

// 扇型、中心と半径、二つの端点
// 現在中心角が180未満の前提
struct sector {
	point o;
	point a, b;
	double r;
	sector(){}
	sector(point O, point A, point B, double _r) :o(O), a(A), b(B), r(_r) {}
};

struct segment : public array<point, 2> {
	segment(const point &a, const point &b) {
		at(0) = a;
		at(1) = b;
	}
};

double cross(const point& a, const point& b) {
	return imag(conj(a)*b);
}

double dot(const point& a, const point& b) {
	return real(conj(a)*b);
}

//角度足し算
double add_rad(double a,double b){
	double ret = a + b;
	if(ret > 2 * PI)ret -= 2 * PI;
	return ret;
}

//なす角(vector)
double angle(const point &a,const point &b) {
	auto tmp = abs(arg(a) - arg(b));
	return min(tmp, 2 * PI - tmp);
}

double angle(const segment &s1,const segment &s2) {
	return angle(s1[1] - s1[0], s2[1] - s2[0]);
}

//点の回転
point rotate(const point &p, double rad) {
	double x = p.real() * cos(rad) - p.imag() * sin(rad);
	double y = p.imag() * cos(rad) + p.real() * sin(rad);
	return point(x, y);
}

//並行
bool isParallel(const point &a, const point &b){
    return abs(cross(a,b)) < EPS;
}
bool isParallel(const segment &a, const segment &b){
    return isParallel(a[1]-a[0], b[1]-b[0]);
}
//直行
bool isOrthogonal(const point &a,const point &b){
	return abs(angle(a,b) - PI / 2) < EPS;
}
bool isOrthogonal(const segment &a,const segment &b){
	return isOrthogonal(a[1]-a[0],b[1]-b[0]);
}

/*
a → b で時計方向に折れて b → c
a → b で半時計方向に折れて b → c
a → b で逆を向いて a を通り越して b → c
a → b でそのまま b → c
a → b で逆を向いて b → c ( または b == c )
*/

int ccw(point a, point b, point c) {
	b -= a; c -= a;
	if (cross(b, c) > EPS)   return +1;       // counter clockwise
	if (cross(b, c) + EPS < 0)   return -1;       // clockwise
	if (dot(b, c) < 0)     return +2;       // c--a--b on line
	if (norm(b) < norm(c)) return -2;       // a--b--c on line
	return 0;
}

bool intersectLL(const segment &l, const segment &m) {
	return abs(cross(l[1] - l[0], m[1] - m[0])) > EPS || // non-parallel
		abs(cross(l[1] - l[0], m[0] - l[0])) < EPS;   // same line
}
bool intersectLS(const segment &l, const segment &s) {
	return cross(l[1] - l[0], s[0] - l[0])*       // s[0] is left of l
		cross(l[1] - l[0], s[1] - l[0]) < EPS; // s[1] is right of l
}
bool intersectLP(const segment &l, const point &p) {
	return abs(cross(l[1] - p, l[0] - p)) < EPS;
}
bool intersectSP(const segment &s, const point &p) {
	auto a = s[0] - p;
	auto b = s[1] - p;
	return (abs(cross(a, b)) < EPS && dot(a, b) <= EPS); // triangle inequality
}
//端点の交差も考える
bool intersectSS(const segment &s, const segment &t) {
	return ccw(s[0], s[1], t[0]) * ccw(s[0], s[1], t[1]) <= 0 &&
		ccw(t[0], t[1], s[0]) * ccw(t[0], t[1], s[1]) <= 0;
}
//端点の交差hは考えない
bool strictIntersectSS(const segment &s, const segment &t) {
	return ccw(s[0], s[1], t[0]) * ccw(s[0], s[1], t[1]) == -1 &&
		ccw(t[0], t[1], s[0]) * ccw(t[0], t[1], s[1]) == -1;
}

point projection(const segment &l, const point &p) {
	double t = dot(p - l[0], l[0] - l[1]) / norm(l[0] - l[1]);
	return l[0] + t*(l[0] - l[1]);
}
point reflection(const segment &l, const point &p) {
	return p + 2. * (projection(l, p) - p);
}
double distanceLP(const segment &l, const point &p) {
	return abs(p - projection(l, p));
}
double distanceLL(const segment &l, const segment &m) {
	return intersectLL(l, m) ? 0 : distanceLP(l, m[0]);
}
double distanceLS(const segment &l, const segment &s) {
	if (intersectLS(l, s)) return 0;
	return min(distanceLP(l, s[0]), distanceLP(l, s[1]));
}
double distanceSP(const segment &s, const point &p) {
	const point r = projection(s, p);
	if (intersectSP(s, r)) return abs(r - p);
	return min(abs(s[0] - p), abs(s[1] - p));
}
double distanceSS(const segment &s, const segment &t) {
	if (intersectSS(s, t)) return 0;
	return min(min(distanceSP(s, t[0]), distanceSP(s, t[1])),
		min(distanceSP(t, s[0]), distanceSP(t, s[1])));
}
double distancePP(const point &a,const point &b){
	return abs(a-b);
}

/*多角形内包判定
half-line crossing method
OUT:0
ON:1
IN:2
*/
int contains(const vector<point>& Poly, const point& p) {
	bool in = false;
	for (int i = 0; i < Poly.size(); ++i) {
		point a = curr(Poly, i) - p, b = next(Poly, i) - p;
		if (imag(a) > imag(b)) swap(a, b);
		if (imag(a) + EPS <= 0 && EPS < imag(b))
			if (cross(a, b) < 0) in = !in;
		if (abs(cross(a, b)) < EPS && dot(a, b) <= EPS) return 1;
	}
	return in ? 2 : 0;
}

/*
OUT:0
ON:1
IN:2
*/
int contain_sector(const sector &sec, point &p){
	if(eq(abs(p - sec.o), sec.r))return 1;
	if(intersectSP(segment(sec.o, sec.a), p))return 1;
	if(intersectSP(segment(sec.o, sec.b), p))return 1;
	if(abs(p - sec.o) + EPS > sec.r)return 0;
	point vec = p - sec.o;
	point vecA = sec.a - sec.o;
	point vecB = sec.b - sec.o;
	if(angle(vec, vecA) + EPS < angle(vecA, vecB) && angle(vec, vecB) + EPS < angle(vecA, vecB))return 2;
	return 0;
}

//交点
point crosspointSS(const segment &l, const segment &m) {
	double A = cross(l[1] - l[0], m[1] - m[0]);
	double B = cross(l[1] - l[0], l[1] - m[0]);
	if (abs(A) < EPS && abs(B) < EPS) return m[0]; // same line
	if (abs(A) < EPS) return point(INF,INF); // !!!PRECONDITION NOT SATISFIED!!!
	return m[0] + B / A * (m[1] - m[0]);
}

vector<point> crosspointCL(const circle &c, const segment &l) {
	auto ret = vector<point>(2, point(INF, INF));
	auto pro_p = projection(l, c.p);
	auto dist = distanceLP(l, c.p);
	if(abs(dist - c.r) < EPS){
		ret[0] = pro_p;
		return ret;
	}
	if(c.r < dist){
		return ret;
	}
	point vec = (l[1] - l[0]) * sqrt(c.r * c.r - dist * dist) / abs(l[1] - l[0]);
	ret[0] = pro_p + vec;
	ret[1] = pro_p - vec;
	return ret;
}

vector<point> crosspointCC(const circle c1, const circle c2) {
	auto ret = vector<point>(2, point(INF, INF));
	auto dist = abs(c2.p - c1.p);
	if(eq(dist, c1.r + c2.r) || eq(dist, abs(c2.r - c1.r))){
		auto tmp = c2.p - c1.p;
		ret[0] = c1.p + tmp * (c1.r / dist);
		return ret;
	}
	if(c1.r + c2.r < dist || dist < abs(c1.r - c2.r)){
		return ret;
	}
	auto alpha = acos((c1.r * c1.r + dist * dist - c2.r * c2.r) / (2 * c1.r * dist));
	auto theta = atan2(c2.p.imag() - c1.p.imag(), c2.p.real() - c1.p.real());
	ret[0] = c1.p + point(cos(theta + alpha) * c1.r, sin(theta + alpha) * c1.r);
	ret[1] = c1.p + point(cos(theta - alpha) * c1.r, sin(theta - alpha) * c1.r);
	return ret;
}

bool isOnSector(const sector sec, const point p) {
	point vec = p - sec.o;
	point vecA = sec.a - sec.o;
	point vecB = sec.b - sec.o;
	if(eq(angle(vec, vecA) + angle(vec, vecB), angle(vecA, vecB)))return true;
	return false;
}

vector<point> crosspointSecS(const sector sec, const segment s) {
	circle c = circle(sec.o, sec.r);
	auto ret = crosspointCL(c, s);
	point inf = point(INF, INF);
	REP(i, 2){
		if(eq(ret[i], inf))continue;
		if(!isOnSector(sec, ret[i])){
			ret[i] = inf;
			continue;
		}
		if(!intersectSP(s, ret[i])){
			ret[i] = inf;
		}
	}
	return ret;
}
vector<point> crosspointSecSec(const sector sec1, const sector sec2) {
	circle c1 = circle(sec1.o, sec1.r);
	circle c2 = circle(sec2.o, sec2.r);
	auto ret = crosspointCC(c1, c2);
	point inf = point(INF, INF);
	REP(i, 2){
		if(!isOnSector(sec1, ret[i])){
			ret[i] = inf;
			continue;
		}
		if(!isOnSector(sec2, ret[i])){
			ret[i] = inf;
		}
	}
	return ret;
}


//凸包
vector<point> convex_hull(vector<point> ps) {
	int n = ps.size(), k = 0;
	sort(ps.begin(), ps.end());
	vector<point> ch(2*n);
	for (int i = 0; i < n; ch[k++] = ps[i++]) // lower-hull
		while (k >= 2 && ccw(ch[k-2], ch[k-1], ps[i]) == -1) --k;
	for (int i = n-2, t = k+1;i >= 0; ch[k++] = ps[i--]) // upper-hull
		while (k >= t && ccw(ch[k-2], ch[k-1], ps[i]) == -1) --k;
	ch.resize(k - 1);
	return ch;
}

//見えるか(可視グラフ用)
bool block_off(const point &a, const point &b, const vector<point> &obj) {
  point m = (a + b) * 0.5;
  bool on = false, in = false;
  for (int j = 0; j < obj.size(); ++j) {
    point c = curr(obj,j), d = next(obj,j);
    if (imag(d) < imag(c)) swap(c, d);
    if (cross(a-c,b-c) * cross(a-d,b-d) < 0 &&    // strictly intersect.
        cross(c-a,d-a) * cross(c-b,d-b) < 0) return true;
    if (cross(a-c,b-c) == 0 && dot(a-c,b-c) < 0) return true;
    if (imag(c) <= imag(m) && imag(m) < imag(d))  // strictly contain.
      if (cross(c-m,d-m) < 0) in = !in;
    if (cross(c-m,d-m) == 0 && dot(c-m,d-m) <= EPS) on = true;
  }
  return !on && in;
}

//面積
double area(const vector<point>& p) {
	double A = 0;
	for (int i = 0; i < p.size(); ++i)
		A += cross(curr(p, i), next(p, i));
	return A / 2.;
}

//凸包判定
bool isConvex(vector<point> poly){
	int sz = poly.size();
	REP(i,sz){
		if(ccw(poly[i],poly[(i+1)%sz],poly[(i+2)%sz]) == -1)return false;
	}
	return true;
}

double convex_diameter(const vector<point> &pt) {
  const int n = pt.size();
  int is = 0, js = 0;
  for (int i = 1; i < n; ++i) {
    if (imag(pt[i]) > imag(pt[is])) is = i;
    if (imag(pt[i]) < imag(pt[js])) js = i;
  }
  double maxd = norm(pt[is]-pt[js]);

  int i, maxi, j, maxj;
  i = maxi = is;
  j = maxj = js;
  do {
    if (cross(diff(pt,i), diff(pt,j)) >= 0) j = (j+1) % n;
    else i = (i+1) % n;
    if (norm(pt[i]-pt[j]) > maxd) {
      maxd = norm(pt[i]-pt[j]);
      maxi = i; maxj = j;
    }
  } while (i != is || j != js);
  return sqrt(maxd); /* farthest pair is (maxi, maxj). */
}

vector<point> convex_cut(const vector<point> P, const segment& l) {
  vector<point> Q;
  for (int i = 0; i < P.size(); ++i) {
    point A = curr(P, i), B = next(P, i);
    if (ccw(l[0], l[1], A) != -1) Q.push_back(A);
    if (ccw(l[0], l[1], A)*ccw(l[0], l[1], B) < 0)
      Q.push_back(crosspointSS(segment(A, B), l));
  }
  return Q;
}

// #################################### end template ######################################

vector<point> makeSquare(point a, point b, ll r) {
	auto vec = (a - b);
	vec *= (r / norm(vec));
	auto rotated_vec = rotate(vec, PI / 2);
	return convex_hull({a + rotated_vec, a - rotated_vec,
											b + rotated_vec, b - rotated_vec});
}

bool canVisible(point p,
								vector<vector<point> > &squares,
								vector<circle> &circles) {
		REP(i, squares.size()){
			if(contains(squares[i], p) == 2)return false;
		}
		REP(i, circles.size()){
			if(distancePP(p, circles[i].p) < circles[i].r + EPS)return false;
		}
		return true;
}

set<point> makePointSet(point start,
												vector<vector<point> > &squares,
												vector<circle> &circles) {

	set<point> ret;
	REP(i, squares.size()){
		auto sq_a = squares[i];
		REP(ii, 4){
			if(!canVisible(sq_a[ii], squares, circles))continue;
			ret.insert(sq_a[ii]);
		}
		REP(j, squares.size()){
			if(i == j)continue;
			auto sq_b = squares[j];
			REP(ii, 4)REP(jj, 4){
				auto p = crosspointSS(segment(sq_a[ii], sq_a[(ii+1)%4]),
														  segment(sq_b[jj], sq_b[(jj+1)%4]));

				if(p == point(INF,INF))continue;
				if(!canVisible(p, squares, circles))continue;
				ret.insert(p);
			}
		}

		REP(j, circles.size()){
			auto cir_b = circles[j];
			REP(ii, 4){
				auto seg = segment(sq_a[ii], sq_a[(ii+1)%4]);
				auto ps = crosspointCL(cir_b, seg);
				for(auto p: ps){
					if(p == point(INF, INF))continue;
					if(!intersectSP(seg, p))continue;
					if(!canVisible(p, squares, circles))continue;
					ret.insert(p);
				}
			}
		}
	}

	REP(i, circles.size()){
		REP(j, circles.size()){
			if(i == j)continue;
			auto ps = crosspointCC(circles[i], circles[j]);
			for(auto p: ps){
				if(p == point(INF, INF))continue;
				if(!canVisible(p, squares, circles))continue;
				ret.insert(p);
			}
		}
	}
	return ret;
}

bool solve() {
	// ################## input ####################
	ll n, x, y, r;cin >> n >> x >> y >> r;
	point start = point(x, y);
	if(n == 0 && x == 0 && y == 0 && r == 0)return false;
	vector<point> points;
	REP(i, n){
		ll a, b;cin >> a >> b;
		points.EB(a, b);
	}

	vector<vector<point> > squares;
	vector<circle> circles;
	REP(i, n){
		circles.EB(points[i], r);
		squares.EB(makeSquare(points[i], points[(i+1)%n], r));
	}

	set<point> pointSet = makePointSet(start, squares, circles);
;

	return true;
}

int main(){
	while(1){
		if(!solve())break;
	}
	return 0;
}
