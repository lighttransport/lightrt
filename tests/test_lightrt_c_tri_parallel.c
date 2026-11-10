/* Axis-parallel rays on box faces, every node format (BVH4/BVH8Q/QF8/Q4).
 * Vertical rays at x = k/g (or z = k/g) over a flat-ish grid mesh lie exactly
 * ON slab planes of many boxes, and every one hits the mesh in exact
 * arithmetic. With -DLRT_TRI_SLAB_ROBUST -DLRT_TRI_LEAF_BOX_EXACT
 * -DLRT_TRI_WATERTIGHT_TRI the test requires 0 misses on every format (the
 * default build reports the clamp-induced slab misses and MT edge misses).
 * Exit 0 = pass. */
#include "lightrt_c_tri.h"
#include <stdio.h>
#include <stdlib.h>
static unsigned long long rs = 1234567;
static float fr(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (float)((rs>>40)*(1.0/16777216.0)); }
int main(void){
  int g=40; size_t n=2*g*g; float *v=malloc(sizeof(float)*9*n); size_t k=0;
  for(int y=0;y<g;y++)for(int x=0;x<g;x++){ float P[4][3]; for(int c=0;c<4;c++){int xx=x+(c&1),yy=y+(c>>1); P[c][0]=(float)xx/g; P[c][1]=0.01f*((xx*7+yy*3)%5); P[c][2]=(float)yy/g;}
    int T[2][3]={{0,1,3},{0,3,2}}; for(int t=0;t<2;t++)for(int c=0;c<3;c++)for(int a=0;a<3;a++) v[k++]=P[T[t][c]][a]; }
  lrt_tri_layout L[4]={LRT_TRI_LAYOUT_BVH4,LRT_TRI_LAYOUT_BVH8Q,LRT_TRI_LAYOUT_BVH8_QF8,LRT_TRI_LAYOUT_BVH8_Q4};
  lrt_tri_scene *sc[4]; lrt_result e;
  for(int i=0;i<4;i++){ lrt_tri_build_options o={LRT_TRI_BUILD_DEFAULT,L[i],0,0}; sc[i]=lrt_tri_scene_build(v,n,&o,&e); if(!sc[i]){printf("build %d fail\n",i);return 1;} }
  int miss[4]={0}, rays=0;
  for(int r=0;r<20000;r++){ lrt_ray ray; float tx=(float)(rand()%(g+1))/g, tz=fr();
    if(r&1){ float t=tx; tx=tz; tz=t; }
    ray.org[0]=tx; ray.org[1]=1.0f+fr(); ray.org[2]=tz; ray.dir[0]=0; ray.dir[1]=-1; ray.dir[2]=0.0f;
    ray.tmin=0; ray.tmax=1e30f; rays++;
    for(int i=0;i<4;i++){ lrt_hit h; if(!lrt_tri_intersect1(sc[i],&ray,&h)) miss[i]++; } }
  printf("%d vertical rays on box faces: misses BVH4=%d BVH8Q=%d QF8=%d Q4=%d\n",rays,miss[0],miss[1],miss[2],miss[3]);
#if defined(LRT_TRI_SLAB_ROBUST) && defined(LRT_TRI_WATERTIGHT_TRI)
  int bad = miss[0] + miss[1] + miss[2] + miss[3];
  printf("RESULT: %s\n", bad ? "FAIL" : "PASS");
  return bad ? 1 : 0;
#else
  printf("RESULT: PASS (report only; robust flags off)\n");
  return 0;
#endif
  }
