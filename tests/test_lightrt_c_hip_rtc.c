/* hiprtc Path-A trace (lightrt_c_hip.c + lightrt_hipew.c, no ROCm SDK at
 * build time) vs the CPU kernel on axis-parallel rays lying exactly on box
 * faces of a grid mesh (every ray hits in exact arithmetic). With
 * -DLRT_TRI_SLAB_ROBUST -DLRT_TRI_LEAF_BOX_EXACT -DLRT_TRI_WATERTIGHT_TRI the
 * test requires 0 GPU misses and GPU == CPU bit for bit (t, prim_id); the
 * default build only reports. Exits 0 (skip) without a HIP device/runtime. */
#include "lightrt_c_tri.h"
#include "lightrt_c_hip.h"
#include <stdio.h>
#include <stdlib.h>
static unsigned long long rs = 1234567;
static float fr(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (float)((rs>>40)*(1.0/16777216.0)); }
int main(void){
  int g=40; size_t n=2*g*g; float *v=malloc(sizeof(float)*9*n); size_t k=0;
  for(int y=0;y<g;y++)for(int x=0;x<g;x++){ float P[4][3]; for(int c=0;c<4;c++){int xx=x+(c&1),yy=y+(c>>1); P[c][0]=(float)xx/g; P[c][1]=0.01f*((xx*7+yy*3)%5); P[c][2]=(float)yy/g;}
    int T[2][3]={{0,1,3},{0,3,2}}; for(int t=0;t<2;t++)for(int c=0;c<3;c++)for(int a=0;a<3;a++) v[k++]=P[T[t][c]][a]; }
  int N=20000; lrt_ray *R=malloc(sizeof(lrt_ray)*N); lrt_hit *H=malloc(sizeof(lrt_hit)*N);
  for(int r=0;r<N;r++){ lrt_ray *ray=&R[r]; float tx=(float)(rand()%(g+1))/g, tz=fr(); if(r&1){float t=tx;tx=tz;tz=t;}
    ray->org[0]=tx; ray->org[1]=1.0f+fr(); ray->org[2]=tz; ray->dir[0]=0; ray->dir[1]=-1; ray->dir[2]=0; ray->tmin=0; ray->tmax=1e30f; }
  int fails = 0; lrt_result e; lrt_hip_engine *eng=lrt_hip_engine_create(NULL,&e); if(!eng){printf("no HIP runtime/device: skipped\n");return 0;}
  for(int L=4;L<=8;L+=4){ lrt_tri_build_options o={LRT_TRI_BUILD_DEFAULT,(lrt_tri_layout)L,0,0}; lrt_tri_scene *s=lrt_tri_scene_build(v,n,&o,&e);
    if(lrt_hip_trace_scene(eng,s,R,(uint32_t)N,H,&e)<0){printf("trace failed: %s (err %d)\n", lrt_hip_engine_last_error(eng), (int)e);return 1;}
    int miss=0, cpumiss=0, diff=0; (void)0; for(int r=0;r<N;r++){ lrt_hit c; int hc=lrt_tri_intersect1(s,&R[r],&c); if(!hc)cpumiss++; if(H[r].prim_id==LRT_TRI_NO_HIT)miss++; if(H[r].prim_id!=c.prim_id||(hc&&H[r].t!=c.t))diff++; }
    printf("BVH%d: %d vertical rays inside the grid: GPU misses %d, CPU misses %d, GPU!=CPU %d\n",L,N,miss,cpumiss,diff); lrt_tri_scene_free(s);
#if defined(LRT_TRI_SLAB_ROBUST) && defined(LRT_TRI_WATERTIGHT_TRI)
    if (miss || diff) fails++;
#endif
  }
  lrt_hip_engine_destroy(eng); printf("RESULT: %s\n", fails ? "FAIL" : "PASS"); return fails ? 1 : 0; }
