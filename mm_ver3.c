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
    "ateam",
    /* First member's full name */
    "pdh90345",
    /* First member's email address */
    "pdh90345",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4             // 시스템의 워드 크기, 헤더와 풋터의 크기도 포함
#define DSIZE 8             // 더블 워드 크기
#define CHUNKSIZE (1 << 12) // 힙을 확장할 때 기본 요청 단위, (4096 바이트)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// 주어진 크기와 할당 비트로 하나의 워드를 패킹, 블록의 헤더와 풋터를 설정할 때 사용
// 메모리 블록의 크기와 할당 상태를 함께 저장
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))              // 주소 p 에서 4바이트 워드를 읽는다 (unsigned int)
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소 p 에 4바이트 워드 값을 val로 설정

// 주소 p 에서 워드를 읽어온다 (블록 크기+할당 상태 정보)
// 0x7비트를 반전시킨 값과 AND연산 -> 하위 3비트를 제외한 나머지 비트가 그대로 유지
// 하위 3비트는 정렬을 위해 사용 -> 하위 3비트는 사용되지 않아 0으로 설정
// 하위 3비트를 제외한 나머지 비트에서 헤더와 풋터를 포함한 블록의 크기정보를 얻을 수 있다
#define GET_SIZE(p) (GET(p) & ~0x7)
// 가장 하위비트 이외에 모든 비트는 0이 된다 -> 할당 비트 값만이 결과로 남는다
#define GET_ALLOC(p) (GET(p) & 0x1)

// (bp : 블록의 페이로드 시작 지점) - 4 바이트(헤더크기) = 헤더 시작 주소
#define HDRP(bp) ((char *)(bp)-WSIZE) // 주어진 블록 포인터 bp에 대해 해당 블록의 헤더 주소 계산

// bp + (GET_SIZE(HDRP(bp)) : 블록의 헤더와 풋터를 포함한 크기) - 8바이트(헤더와 풋터의 총 크기)
// = 풋터의 시작 위치 (사실상 페이로드가 끝나는 지점과 같다)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 풋터 주소 계산

// 다음 페이로드 시작주소
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 주어진 bp에 대해 다음 블록 시작주소 계산
// 이전 페이로드 시작주소
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE))) // 이전 시작주소 계산

/*
 * mm_init - initialize the malloc package.
 */
static char *heap_listp; // 항상 프롤로그 블록(헤더와 풋터만으로 구성된 블록)을 가리킨다 (해제x) (힙의 시작부분)
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
char *last_visited;
int mm_init(void)
{
    // 32비트 공간을 메모리 시스템에서 증가시키려고 시도
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // msm_sbrk 실패하면 -1 반환 (성공하면 확장전 끝 포인터 반환)
    {
        return -1; // 실패하면 -1
    }
    PUT(heap_listp, 0);                            // 첫번째 블록을 0으로 설정하여 페이로드 블록이 정렬되게 (패딩 역할)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더, DSIZE -> 블록크기
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 풋터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 헤더(크기는 0, 할당 비트는 1)
    heap_listp += (2 * WSIZE);                     // 두 워드 뒤로 이동시켜 프롤로그 풋터 바로 뒤 가르킨다

    // extend_heap 호출하여 CHUNKSIZE만큼 힙을 추가로 확장하고 초기 크기의 자유 블록 생성
    // extend_heap에 워드사이즈로 변환해서 보낸다
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }
    last_visited = (char *)heap_listp;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 짝수가 아닐경우 짝수로 만들어서 워드의 크기를 곱하여 바이트 단위로 계산
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // mem_sbrk함수를 호출하여 요청된 크기만큼 힙 확장
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    // 확장된 메모리 블록의 풋터와 헤더 초기화 (할당 안됨)
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    // 새로운 에필로그 헤더 설정
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 새로 확장된 블록이 이전의 자유 블록과 인접한 경우,
    // 이들 블록을 병합하여 하나의 자유블록 생성
    return coalesce(bp);
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
//         return NULL;
//     else
//     {
//         *(size_t *)p = size;
//         return (void *)((char *)p + SIZE_T_SIZE);
//     }
// }

void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 사이즈
    size_t extendsize; // 확장 크기
    char *bp;

    if (size == 0) // 크기가 0인 요청은 무효
    {
        return NULL;
    }

    if (size <= DSIZE) // 더블 워드 이하인 경우 최소 블록 크기로 반환
    {
        asize = 2 * DSIZE; // 8바이트는 더블 워드 정렬, 8바이트는 헤더와 풋터의 오버헤드를 위해
    }
    else // 더블워드 크기로 반올림
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) // asize에 맞는 자유 블록을 리스트에서 검색
    {
        place(bp, asize); // 적합한 블록이 발견되면 이 블록을 요청된 크기에 맞게 할당
        last_visited = bp;
        return bp; // 해당 블록 포인터 리턴
    }

    extendsize = MAX(asize, CHUNKSIZE);                 // 못찾을 경우 확장 크기 결정
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) // 힙 확장
    {
        return NULL;
    }
    place(bp, asize); // 확장된 힙에서 할당 처리
    last_visited = bp;
    return bp;
}

// static void *find_fit(size_t asize)
// {
//     // First-fit search
//     void *bp; // 현재 검사중인 블록

//     // 힙의 시작 부분 부터
//     // 에필로그 헤더에 도착할때 까지 (사이즈가 0)
//     // 다음 블록으로
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
//     {
//         // 할당 되지 않은 상태 면서 요청된 크기보다 크거나 같을 경우
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
//         {
//             return bp; // 반환
//         }
//     }
//     return NULL;
// }

static void *find_fit(size_t adjusted_size)
{
    // Next-fit
    char *bp = last_visited; // 초기화

    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) // 힙의 끝까지
    {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjusted_size) // 요구 크기보다 크거나 같으면
        {
            last_visited = bp;
            return bp;
        }
    }

    bp = heap_listp;
    while (bp < last_visited) // 못찾으면 처음부터 다시
    {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjusted_size)
        {
            last_visited = bp;
            return bp;
        }
    }

    return NULL;
}

// static void *find_fit(size_t asize)
// {
//     // Best-fit search
//     void *bp; // 현재 검사중인 블록

//     void *best_fit = NULL;
//     size_t min_diff = (2UL << 31) - 1; // 최소 차이를 저장

//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
//     {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
//         {
//             size_t diff = GET_SIZE(HDRP(bp)) - asize;
//             if (diff < min_diff)
//             {
//                 best_fit = bp;
//                 min_diff = diff;
//                 if (diff == 0)
//                     break; // 완벽하게 맞는 블록을 찾은 경우
//             }
//         }
//     }
//     return best_fit;
// }
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 자유 블록의 크기

    if ((csize - asize) >= (2 * DSIZE))        // 할당 후 남은 크기가 16바이트 이상이면 블록 분할
    {                                          // -> 메모리 낭비 최소화, 나중에 다른 요청에 사용할 수 있도록
        PUT(HDRP(bp), PACK(asize, 1));         // 현재 블록의 헤더 풋터를
        PUT(FTRP(bp), PACK(asize, 1));         // 요청된 크기로 설정, 할당된 상태로
        bp = NEXT_BLKP(bp);                    // 다음 블록
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 남은 부분을 자유 블록으로
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else // 남은 크기가 작으면
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 전부 다 할당 되도록
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // bp가 가리키는 블록의 헤더에서 크기를 읽어온다

    PUT(HDRP(bp), PACK(size, 0)); // 헤더와 풋터를 자유 블록으로 업데이트
    PUT(FTRP(bp), PACK(size, 0)); // 크기는 그대로 할당 비트만 0
    coalesce(bp);                 // 해제된 블록이 자유 블록과 인접해 있을 경우 병합
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 할당 상태
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) // 이전 블록, 다음 블록 모두 할당된 상태 (case 1)
    {
        return bp; // 병합이 필요 없으므로 그대로 반환
    }
    else if (prev_alloc && !next_alloc)        // 이전 블록 할당, 다음 블록 자유 (case 2)
    {                                          // 현재 블록과 다음 블록 병합
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록 크기를 현재 블록 크기에 더한다
        PUT(HDRP(bp), PACK(size, 0));          // 현재 블록의 헤더와 풋터를 새로운 크기로 업데이트
        PUT(FTRP(bp), PACK(size, 0));          // size는 변환된 블록 크기
    }
    else if (!prev_alloc && next_alloc)          // 이전 블록 자유, 다음 블록 할당 (case 3)
    {                                            // 이전 블록과 현재 블록 병합
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 이전 블록 크기를 현재 블록 크기에 더한다
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록의 풋터를 새로운 크기로
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더를 새로운 크기로
        bp = PREV_BLKP(bp);                      // bp를 이전 블록의 시작 주소로
    }
    else                                                                       // 이전 블록 자유, 다음 블록 자유
    {                                                                          // 현재 블록과 인접한 두 자유 블록을 모두 병합
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 현재 사이즈에 이전 블록, 다음 블록 사이즈를 더함
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                               // 이전 블록 헤더를 새로운 크기로
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                               // 다음 블록 풋터를 새로운 크기로
        bp = PREV_BLKP(bp);                                                    // bp를 이전 블록의 시작 주소로
    }
    last_visited = bp;

    return bp; // 수정된 bp 반환
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */

void *mm_realloc(void *bp, size_t size) // ptr : 재할당 하고자 하는 블록포인터, size : 사용자가 요청한 새로운 크기
{
    void *oldbp = bp;
    void *newbp;
    size_t copySize;
    if (size == 0)
    {
        mm_free(oldbp);
        return NULL;
    }

    newbp = mm_malloc(size);
    if (newbp == NULL)
        return NULL;
    size_t oldSize = GET_SIZE(HDRP(oldbp)); // 블록 사이즈 저장
    if (size < oldSize)                     // 요청된 크기가 기존 크기 보다 작으면
        copySize = size;                    // 블록 사이즈를 줄인다
    else
    {
        copySize = oldSize;
    }
    memcpy(newbp, oldbp, copySize); // 데이터 복사
    mm_free(oldbp);                 // 예전 블록 반환
    return newbp;
}