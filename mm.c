 #include <stdio.h>
 #include <stdlib.h>
 #include <assert.h>
 #include <unistd.h>
 #include <string.h>
 
 #include "mm.h"
 #include "memlib.h"
 
 team_t team = {
     "ateam",
     "yechan",
     "cksdid1363@gmail.com",
     "",
     ""};
 
 /* single word (4) or double word (8) alignment */
 #define ALIGNMENT 8
 
 /* rounds up to the nearest multiple of ALIGNMENT */
 #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
 
 #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
 
 /* 가용 리스트 조작을 위한 기본 상수 및 매크로 정의*/
 #define WSIZE 4        // 워드 크기 (헤더/풋터에 사용) : 4바이트
 #define DSIZE 8        // 더블 워드 크기(정렬 단위) : 8바이트
 #define CHUNKSIZE (1<<12)  // 힙을 확장할 때 한 번에 늘리는 크기 

 #define MAX(x,y) ((x) > (y) ? (x) : (y)) 

 /* 크기와 할당 비트를 하나의 워드로 결합 */
 #define PACK(size,alloc) ((size)|(alloc)) // size : 블록 크기, alloc : 할당 여부( 0 또는 1)
 
 /* 주소 p에서 워드 읽기, 쓰기*/
 #define GET(p)     (*(unsigned int *)(p))  // p가 가리키는 워드(4바이트)를 읽어서 unsigned int로 반환
 #define PUT(p,val) (*(unsigned int *)(p) = (val)) // p가 가리키는 워드에 val을 저장 

 /* 워드에서 블록 크기와 할당 여부 추출 */
 #define GET_SIZE(p)    (GET(p) & ~0x7)     // 블록크기를 반환 (하위 3비트를 제외한 상위비트를 가져옴)
 #define GET_ALLOC(p)    (GET(p )& 0x1)     // 할당여부를 반환(0: free, 1: allocated) / 최하위 비트를 봄

 /* 블록 포인터 (bp)로부터 헤터/풋터 주소 계산   (bp : 페이로드의 시작주소를 가리키는 포인터)  */
 #define HDRP(bp)       ((char *)(bp) - WSIZE)        // HDRP(bp): 블록 헤더 주소 = bp(페이로드 시작) 바로 앞 WSIZE 바이트
 #define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)     // FTRP(bp): 블록 풋터 주소 = bp + 블록 전체 크기(GET_SIZE) - DSIZE

 /* 블록 포인터 (bp)로 부터 다음/ 이전 블록의 페이로드 시작 주소 계산*/
 #define NEXT_BLKP(bp)      ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))    // NEXT_BLKP(bp): 다음 블록의 페이로드 = bp + 현재 블록 크기
 #define PREV_BLKP(bp)      ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))    // PREV_BLKP(bp): 이전 블록의 페이로드 = bp - 이전 블록 크기

 #define GET_SUCC(bp)     (*(void **)((char *)(bp)+WSIZE))                //더블 포인터인 이유는? *(bp)를 쓰고 싶은데 bp의 타입은 void 이기때문에 간접참조를 못함 따라서 더블 포이터를 써서 간접 참조 하게 함!(하지만 이중포인터는 아님!)
 #define GET_PRED(bp)     *(void **)(bp)                                  // pred는 bp 그 자체    
 
 static char* heap_listp;
 static char* free_listp;
 
static void insert_free_list(void *bp){            //LIFO방식으로 넣을꺼임
    // 새로 삽입되는 free_block을 앞에다가 넣어야됨(LIFO)
    // 새로 삽입되는 free_block의 succ를 NEXT_FREE_BLKP의 prev와 연결
    GET_PRED(bp) = NULL;                                    // bp의 이전(prev) 포인터를 NULL로 설정 (헤드가 되므로 이전 노드가 없음)
    GET_SUCC(bp) = free_listp;                              // bp의 다음(next) 포인터를 현재 free_listp(기존 헤드)로 설정
    if (free_listp != NULL) GET_PRED(free_listp) = bp;      // 기존 헤드가 있으면, 그 블록의 prev를 bp로 연결
    free_listp = bp;                                        // free_listp를 bp로 갱신하여 헤드로 설정

}

/* free 리스트에서 블록 bp를 제거 */
static void remove_free_list(void *bp){
    //삭제하려는 free_block의 succ와 prev의 연결을 끊어야 함
    //PREV_FREE_BLKP의 succ를 NEXT_FREE_BLKP의 prev와 연결
    if(GET_PRED(bp) == NULL){                               // 삭제하려는 블록이 맨 앞일경우
        free_listp = GET_SUCC(bp);                          // free_listp를 bp의 다음 노드로 옮겨 헤드 갱신
        if (GET_SUCC(bp) != NULL)                           // 새 헤드가 존재하면,
            GET_PRED(GET_SUCC(bp)) = NULL;                  // 그 헤드의 prev를 NULL로 설정
    }
    else{                                                   // 맨 앞이 아닐 경우(중간 혹은 마지막)
        GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);              // 이전 노드의 next를 bp의 다음 노드와 연결
        if(GET_SUCC(bp)!=NULL){                             // 만약 bp의 다음 노드가 있으면, 
            GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);          // 그 노드의 prev를 bp의 이전 노드와 연결
        }    
    }
}

 // 가용 리스트(heap_listp)에서 요청크기(asize)에 맞는 첫번째 블록을 찾아 리턴하는 함수
 static void *find_fit(size_t asize){

    /* First-fit search */
    void *bp;   // bp(블록 포인터) : 페이로드 시작 주소

    for (bp = free_listp; bp != NULL; bp  = GET_SUCC(bp)){                      // free_listp부터 시작해, free_list가 끝날때까지     
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){             // 현재 블록이 free인지 그리고 크기가 충분한지 확인
            return bp;                                                          //조건 만족시 이 bp를 반환
        }
    }
    return NULL;                                                                // 끝까지 못 찾으면 NULL을 반환
 }


 // 빈 블록 bp를 asize만큼 할당하고, 남는 공간이 충분하면 분할하는 함수 
 static void place(void *bp, size_t asize)
 {
    size_t csize = GET_SIZE(HDRP(bp));          // cize : 현재 빈 블록 전체 크기(헤더 + 페이로드 + 풋터

    // 분할 가능한지 검사 
    if((csize - asize) >= (2*DSIZE)){           // 남는 공간(csize-asize)이 최소 블록 크기(2*DSIZE) 보다 크거나 같으면 분할 처리
        // 앞쪽(asize) 부분을 할당 블록으로 표시
        PUT(HDRP(bp), PACK(asize, 1));          // 헤더에 size = asize, alloc = 1
        PUT(FTRP(bp), PACK(asize, 1));          // 푸터도 동일하게 기록
        bp = NEXT_BLKP(bp);                     // bp를 "다음 블록 위치"로 옮겨서 남는 공간 블록 처리
        // 남는 뒷부분 분을 새 빈 블록으로 초기화
        PUT(HDRP(bp), PACK(csize-asize,0));     // 헤더에 남은 크기, alloc = 0 
        PUT(FTRP(bp), PACK(csize-asize,0));     // 푸터에도 동일하게 기록
        insert_free_list(bp);
    }
    // 분할 여유가 없으면 블록 전체를 한 덩어리로 할당
    else{
        PUT(HDRP(bp), PACK(csize,1));           // 헤더에 size = csize, alloc = 1  
        PUT(FTRP(bp), PACK(csize,1));           // 푸터에도 동일하게 기록
    }
 }

 // 현재 블록 bp를 기준으로 이전(prev) 및 다음(next) 블록과 free여부 를 확인하여 4가지 경우에 맞춰 블록을 병합하는 함수 -> 반환값 : 병합 후 블록의 페이로드(bp)
 static void* coalesce(void *bp)  //remove와 insert인 함수가 필요
 {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 (prev_alloc=1, next_alloc=1 → 양쪽 모두 할당됨)
    if (prev_alloc && next_alloc){
        insert_free_list(bp);
        return bp;  // 병합 없이 그대로 반환
    }

    // case 2 (이전은 할당됨, next는 free_block) -> 현재블록 + 다음 블록 병합
    else if(prev_alloc && !next_alloc){
        remove_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  //다음 블록의 크기만큼 확장
        //헤더와 풋터에 새 크기로 기록
        PUT(HDRP(bp), PACK(size, 0));           
        PUT(FTRP(bp), PACK(size, 0));
        
    }

    // case 3 (이전은 free_block, next는 할당됨) -> 이전 블록 + 현재 블록 병합
    else if(!prev_alloc && next_alloc){
        remove_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      //이전 블록의 크기만큼 확장
        PUT(FTRP(bp), PACK(size, 0));               //풋터에는 현재 블로 풋터자리
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    //헤더에는 이전 블록 헤더 자리 갱신
        bp = PREV_BLKP(bp); 
        
    }

    // case4 (이전과 다음 블록 둘다 free_block) -> 이전 + 현재 + 다음 모두 병합 
    else{
        remove_free_list(NEXT_BLKP(bp));
        remove_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 크기 + 현재 블록 크기 + 다음 블록 크기 합산
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));      // 헤더는 이전 블록 헤더 자리 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));     // 풋터는 다음 블록 풋터 자리 
        bp = PREV_BLKP(bp);     // bp를 이전 블록 페이로드 시작으로 이동
        
    }
    insert_free_list(bp);
    return bp;
 }


 static void *extend_heap(size_t words)
 {
    char *bp;       // 새로 확장된 블록의 페이로드 시작 주소를 받을 포인터
    size_t size;    // 요청할 바이트 단위 크기

    // size는 바이트 단위 요청 크기
    size = (words % 2) ? (words +1) *WSIZE : words * WSIZE; // 요청한 워드 수(words)가 홀수 면 +1 워드해서 짝수 로 맞춤 -> DSIZE(8바이트) 정렬을 유지하기 위해서 
    
    // mem_sbrk로 실제 힙을 size 바이트만큼 확장
    if ((long)(bp = mem_sbrk(size)) == -1)                  // 확장 실패시 null 반환
        return NULL;


    // 방금 확보한 영역을 "free block"으로 초기화
    PUT(HDRP(bp), PACK(size, 0));       
    PUT(FTRP(bp), PACK(size, 0));

    // 새 에필로그 헤더를 블록뒤에 설정
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));                    // 크기 0, 할당됨 1 상태로 힙 끝을 표시

    // 이전 블록이 free blockdlaus 병합(coalesce) 처리하고 새로 합쳐진(또는 그대로인) 블록의 bp를 반환
    return coalesce(bp);

 }
 /*
  * mm_init - initialize the malloc package.
  */
 int mm_init(void) //최초 가용 블록으로 힙 생성하기 (메모리 시스템에서 4워드 가져와서 빈 가용리스트를 만들 수 있도록 초기화한다.)
 {
/* 6 워드(6 * WSIZE = 24바이트)로 초기 힙 영역 확보
       - 1st word : 패딩 (정렬을 위해 사용)
       - 2nd word : 프로로그 블록 헤더 (크기=DSIZE, 할당=1)
       - 3rd word : free 리스트용 pred 포인터 (초기 NULL)
       - 4th word : free 리스트용 succ 포인터 (초기 NULL)
       - 5th word : 프로로그 블록 푸터 (헤더와 동일)
       - 6th word : 에필로그 헤더 (크기=0, 할당=1) */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)     
        return -1;
    PUT(heap_listp , 0);                                     // 1) 패딩
    PUT(heap_listp + (1*WSIZE), PACK(2*DSIZE,1));            // 2) 프로로그 헤더
    PUT(heap_listp + (2*WSIZE), NULL);                       // 3) pred = NULL
    PUT(heap_listp + (3*WSIZE), NULL);                       // 4) succ = NULL
    PUT(heap_listp + (4*WSIZE), PACK(2*DSIZE,1));            // 5) 프로로그 푸터
    PUT(heap_listp + (5*WSIZE), PACK(0,1));                  // 6) 에필로그 헤더
    heap_listp += (2*WSIZE);                                 // bp를 프로로그 블록 바로 뒤(첫 가용 블록 위치)로 옮김 
    
    free_listp = NULL;                                       // free 리스트 초기화 


    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)               // CHUNKSIZE 만큼 힙 확장하여 첫 가용 블록 생성 
        return -1;
    return 0;
 }
 
 /*
  * mm_malloc - Allocate a block by incrementing the brk pointer.
  *     Always allocate a block whose size is a multiple of the alignment.
  */

  //내부 가용 리스트에서 적절한 공간을 찾아 할당해 주고, 모자랄 땐 힙을 키워서라도 요청한 메모리를 돌려주는 함수
 void *mm_malloc(size_t size)   
 {
    size_t asize;           // 요청 크기에 오버헤드(헤더, 풋터)와 정렬 요구를 반영한 최종 블록 크기
    size_t extendsize;      // 힙을 새로 확장할 때 사용할 크기
    char *bp;               // 할당된 블록의 페이로드 시작 주소를 받을 포인터

    // 잘못된 요청(크기가 0) 무시
    if(size == 0){
        return NULL;
    }

    // 블록의 크기 조정
    if (size <= DSIZE){     // size <= DSIZE(8바이트)면 
        asize = 2*DSIZE;    // 2*DSIZE로 할당 (헤더+풋터+정렬을 위한 최소 공간 확보)
    }else{      // 그외에는 요청 size + 오버헤드(DSIZE)를 DSIZE 단위로 올림
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); //??
    }

    // 가용 리스트에서 asize 크기에 맞는 블록 검색
    if ((bp = find_fit(asize)) != NULL){
        remove_free_list(bp);    
        place(bp, asize);       //found : 해당 블록을 place()로 분할,할당 처리 후 리턴
        return bp;      
    }
    
    // 맞는 블록이 없으면 힙을 더 늘려야 함 
    extendsize = MAX(asize, CHUNKSIZE);     // -> 요청 크기가 작아도 CHUNKSIZE(4096B)단위로 늘려 분할,병합 오버헤드를 줄임
    
    // 힙 확장 : extendsize/WSIZE 워드를 요청 -> 실패시 NULL 반환
    if ((bp  = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }

    remove_free_list(bp);
    // 확장한 새 블록에 place() 적용하여 할당 처리
    place(bp,asize);
    return bp;
 }
 
 /*
  * mm_free - Freeing a block does nothing.
  */
 void mm_free(void *bp)    // 블록을 해제하고, 주변의 빈 블록과 경계 태그를 이용해 병합하는 함수 / *ptr : payload 시작을 가리키는 포인터
 {
    size_t size = GET_SIZE(HDRP(bp));   // 헤더에서 이 이블록의 전체 크기(헤더+페이로드+풋터)를 읽어온다.

    // 해제된(free) 블록으로 표시 , PACK(size,0) -> size 와 alloc 비트 = 0 (free)
    PUT(HDRP(bp), PACK(size, 0));   // 헤더 갱신
    PUT(FTRP(bp), PACK(size, 0));   // 푸터 갱신
    
    // 주변 블록이 free상태면 하나로 합쳐서 외부 단편화 줄이기
    coalesce(bp);
 }
 
 /*
  * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
  */
 void *mm_realloc(void *ptr, size_t size)   //ptr은 페이로드 시작주소
 {
     void *oldptr = ptr;
     void *newptr;
     size_t copySize;
 
     newptr = mm_malloc(size);  //사이즈만큼 새로 할당받기
     if (newptr == NULL)    //예외처리
         return NULL;
     //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
     copySize = GET_SIZE(HDRP(oldptr)) - DSIZE; // 딱 페이로드 사이즈
     if (size < copySize)               // 복사하는데 size 만큼만 복사할거니까
         copySize = size;               // 사이즈를 줄인다.
     memcpy(newptr, oldptr, copySize);  // 메모리를 카피
     mm_free(oldptr);
     return newptr;
 }