/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "C&C",
    /* First member's full name */
    "daltong",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/**************************************************************/
/* Basic contants and macros */
#define WSIZE 4             // 워드 사이즈
#define DSIZE 8             // 더블 워드 사이즈
#define CHUNKSIZE (1 << 12) // 초기 가용 블록과 힙 확장을 위한 기본 크기

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))              // p가 참조하는 워드를 읽어서 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p가 가리키는 워드에 val을 저장한다.

/* Read the size and allocated fileds from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) // p에 있는 헤더 혹은풋터의 size 리턴
#define GET_ALLOC(p) (GET(p) & 0x1) // p에 있는 헤더 혹은풋터의 할당비트 리턴

/* Given block ptr bp, compute address of its header and footer */
// 블록포인터 bp가 주어지면 각각 블록의 헤더와 풋터를가리키는 포인터를 리턴함
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute adress of next and previous blocks */
// 이전과 다음 블록의 블록 포인터를 리턴
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

static char *heap_listp;
static char *last_bp = NULL;

/**************************************************************/

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * coalesce - initialize the malloc package.
 */
static void *coalesce(void *bp)
{
    // printf("coalesce 시작함\n");
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        // printf("case1 들어옴\n");
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {
        // printf("case2 들어옴\n");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        // printf("case2 끝남\n");
    }
    else if (!prev_alloc && next_alloc)
    {
        // printf("case3 들어옴\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        // printf("case3 끝남\n");
    }
    else
    {
        // printf("case4 들어옴\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        // printf("case4 끝남\n");
    }
    // printf("coalesce 끝남\n");
    return bp;
}

/*
 * extend_heap - initialize the malloc package.
 */
static void *extend_heap(size_t words)
{
    // printf("maxSize: %d\n", words);
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // static char *heap_listp;
    /*
    C 코드에서 (void *)-1은 일반적으로 함수나 작업이 실패했음을 나타내기 위해 사용됩니다.
    보통 이 표현은 함수나 작업이 유효한 포인터를 반환하지 못했을 때, 특히 메모리 할당과 같은 작업에서 사용됩니다.
    mem_sbrk(4*WSIZE) 함수가 호출되어 메모리 할당을 시도하고, 그 결과로 유효한 메모리 주소를 얻지 못했을 때,
    해당 함수는 일반적으로 (void *)-1을 반환합니다. 이 값은 일반적으로 C에서 실패를 나타내는 특수한 값을 나타냅니다.
    따라서 heap_listp 변수에 할당되는 값이 (void *)-1인 경우, 메모리 할당이 실패했음을 나타냅니다.
    */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    // printf("heap_listp: %p\n",heap_listp);
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    // printf("Prologue header: %p , (1*WSIZE): %d\n",heap_listp + (1*WSIZE),(1*WSIZE));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    // printf("Prologue footer: %p , (1*WSIZE): %d\n",heap_listp + (2*WSIZE),(2*WSIZE));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); /* Epilogue header */
    // printf("Epilogue header: %p , (1*WSIZE): %d\n",heap_listp + (3*WSIZE),(3*WSIZE));
    heap_listp += (2 * WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
// void *mm_malloc(size_t size)
// {
//     int newsize = ALIGN(size + SIZE_T_SIZE);
//     void *p = mem_sbrk(newsize);
//     if (p == (void *)-1)
// 	return NULL;
//     else {
//         *(size_t *)p = size;
//         return (void *)((char *)p + SIZE_T_SIZE);
//     }
// }

static void *find_fit(size_t asize)
{
    char *new_bp = NULL;
    /**********************  first fit  ************************************/
    // char *new_bp = heap_listp;
    // // printf("new_bp: %p, size: %d, alloc: %d \n", new_bp, GET_SIZE(new_bp),GET_ALLOC(new_bp));
    // do{
    //     //printf("뜌땨\n");
    //     if (GET_SIZE(HDRP(new_bp))>asize && GET_ALLOC(HDRP(new_bp))== 0){
    //         //printf("공간 찾음!\n");
    //         return new_bp;
    //     }
    //     else {
    //         new_bp= NEXT_BLKP(new_bp);
    //         //printf("new_bp: %p, size: %d, alloc: %d \n", new_bp, GET_SIZE(new_bp),GET_ALLOC(new_bp));
    //     }
    // }while(GET_SIZE(HDRP(new_bp))>0 );
    /********************************************************************/
    /**********************  next fit  ************************************/
    if (last_bp == NULL)
    {
        new_bp = heap_listp;
    }
    else
    {
        new_bp = last_bp;
    }
    // printf("new_bp: %p, size: %d, alloc: %d \n", new_bp, GET_SIZE(new_bp),GET_ALLOC(new_bp));
    do
    {
        // printf("뜌땨\n");
        if (GET_SIZE(HDRP(new_bp)) > asize && GET_ALLOC(HDRP(new_bp)) == 0)
        {
            // printf("공간 찾음!\n");
            last_bp = new_bp;
            return new_bp;
        }
        else
        {
            new_bp = NEXT_BLKP(new_bp);
            // printf("new_bp: %p, size: %d, alloc: %d \n", new_bp, GET_SIZE(new_bp),GET_ALLOC(new_bp));
        }
    } while (GET_SIZE(HDRP(new_bp)) > 0);

    /********************************************************************/
    /**********************  best fit  ************************************/
    // char *new_bp = heap_listp;
    // char *best_bp = new_bp;
    // size_t min_size= -1;
    // // printf("요구 사이즈 : %d  \n",asize);
    // while(1){
    //     new_bp= NEXT_BLKP(new_bp);
    //     size_t now_size = GET_SIZE(HDRP(new_bp));
    //     // printf("이번 사이즈 : %d  \n",now_size);
    //     if(now_size<=0){
    //         break;
    //     }
    //     else{
    //         if(GET_ALLOC(HDRP(new_bp))== 0 && now_size>=asize && ( min_size == -1|| min_size>= now_size)){
    //             best_bp = new_bp;
    //             min_size = now_size;
    //             // printf("새로운 사이즈:%d \n",min_size);
    //         }
    //         // printf("best_bp:%p, new_bp:%p\n",best_bp, new_bp);
    //     }
    // }
    // if (min_size != -1){
    //     // printf("최소 사이즈: %d\n\n", min_size);
    //     return best_bp;
    // }
    /********************************************************************/
    return NULL;
}

static void place(void *bp, size_t asize)
{

    size_t lest_size = GET_SIZE(HDRP(bp));
    if ((lest_size - asize >= (2 * DSIZE)))
    {
        PUT(HDRP(bp), PACK(asize, 1)); /* header */
        PUT(FTRP(bp), PACK(asize, 1)); /* footer */
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(lest_size - asize, 0)); /* header */
        PUT(FTRP(bp), PACK(lest_size - asize, 0)); /* footer */
    }
    else
    {
        PUT(HDRP(bp), PACK(lest_size, 1)); /* header */
        PUT(FTRP(bp), PACK(lest_size, 1)); /* footer */
    }
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    /* 사이즈 0 요청해서 무시함 */
    if (size == 0)
        return NULL;

    /* 최소 사이즈(16바이트(헤더8+푸터8))보다 작으면 최소 사이즈맞춤 */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
// void mm_free(void *ptr)
// {
// }

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    last_bp = coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; // 현재주소
    void *newptr;       // 이사할 집 주소
    size_t copySize;    // 우리집 식구 크기

    // 이사할 주소 받아옴
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    // printf("SIZE_T_SIZE: %d\n",SIZE_T_SIZE);

    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr; // 이전 포인터
//     void *newptr; // 새로 메모리 할당할포인터

//     size_t originsize = GET_SIZE(HDRP(oldptr)); // 원본 사이즈
//     size_t newsize = size + DSIZE; // 새 사이즈

//     // size 가 더 작은 경우
//     if (newsize <= originsize) {
//         return oldptr;
//     } else {
//         size_t addSize = originsize + GET_SIZE(HDRP(NEXT_BLKP(oldptr))); // 추가 사이즈 -> 헤더 포함 사이즈
//         if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (newsize <= addSize)){ // 가용 블록이고 사이즈 충분
//             PUT(HDRP(oldptr), PACK(addSize, 1)); // 새로운 헤더
//             PUT(FTRP(oldptr), PACK(addSize, 1)); // 새로운 푸터
//             return oldptr;
//         } else {
//             newptr = mm_malloc(newsize);
//             if (newptr == NULL)
//                 return NULL;
//             memmove(newptr, oldptr, newsize); // memcpy 사용 시, memcpy-param-overlap 발생
//             mm_free(oldptr);
//             return newptr;
//         }
//     }
// }