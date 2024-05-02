/* 프로그램이 사용하는 헤더 파일 포함 */
#include <stdio.h>  // 표준 입출력 함수 사용
#include <stdlib.h> // 표준 라이브러리 함수 사용
#include <assert.h> // 검증을 위한 함수 사용
#include <unistd.h> // 시스템 호출을 위한 함수 사용
#include <string.h> // 문자열 관련 함수 사용

/* 자체 정의된 헤더 파일 포함 */
#include "mm.h"     // 메모리 관리 관련 헤더 파일
#include "memlib.h" // 메모리 시스템을 위한 헤더 파일

/* 팀 정보 구조체 정의 */
team_t team = {
    "ateam",
    "Harry Bovik",
    "bovik@cs.cmu.edu",
    "",
    ""};

/* 메모리 정렬을 위한 매크로 정의 */
#define ALIGNMENT 8                                     // 메모리를 8바이트 단위로 정렬
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 주어진 사이즈를 ALIGNMENT의 배수로 정렬

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t의 크기를 ALIGNMENT에 맞춘 값
#define WSIZE 4                             // Word의 크기
#define DSIZE 8                             // Double word의 크기
#define CHUNKSIZE (1 << 12)                 // 초기 힙 크기 및 확장 단위

/* 유틸리티 매크로 */
#define MAX(x, y) ((x) > (y) ? (x) : (y))    // 두 값 중 최대값 반환
#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 패킹

#define GET(p) (*(unsigned int *)(p))              // 주소 p에서 4바이트 읽기
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소 p에 4바이트 쓰기

#define GET_SIZE(p) (GET(p) & ~0x7) // 헤더에서 블록 크기 읽기
#define GET_ALLOC(p) (GET(p) & 0x1) // 헤더에서 할당 비트 읽기

#define HDRP(bp) ((char *)(bp)-WSIZE)                        // 블록 포인터에서 헤더의 주소 계산
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 포인터에서 푸터의 주소 계산

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록의 주소 계산
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록의 주소 계산

// 함수 프로토타입 선언
int mm_init(void);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);
void *heap_listp; // 힙의 시작 부분을 가리키는 포인터

/*
 * mm_init - malloc 패키지 초기화
 */
int mm_init(void)
{
    // 초기 힙 영역 확보
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);                            // 힙 시작 부분에 패딩 삽입
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더 설정
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터 설정
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 헤더 설정
    heap_listp += (2 * WSIZE);                     // 힙 리스트 포인터를 초기 위치로 설정
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)    // 힙 확장
        return -1;
    return 0;
}

/* coalesce - 인접한 빈 블록을 통합 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 할당 상태 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 할당 상태 확인
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록의 크기 확인

    if (prev_alloc && next_alloc) // 양쪽 블록 모두 할당된 경우
    {
        return bp; // 통합 없이 반환
    }

    else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록 크기 추가
        PUT(HDRP(bp), PACK(size, 0));          // 현재 블록의 헤더 업데이트
        PUT(FTRP(bp), PACK(size, 0));          // 새 푸터 위치에 푸터 설정
    }

    else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 이전 블록 크기 추가
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록의 푸터 업데이트
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더 업데이트
        bp = PREV_BLKP(bp);                      // 현재 블록 포인터 이전 블록으로 업데이트
    }

    else // 양쪽 블록 모두 빈 경우
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더 업데이트
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록의 푸터 업데이트
        bp = PREV_BLKP(bp);                      // 현재 블록 포인터 이전 블록으로 업데이트
    }

    return bp;
}

/* extend_heap - 힙을 주어진 단어 수만큼 확장 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 확장할 크기를 8의 배수로 맞춤
    if ((long)(bp = mem_sbrk(size)) == -1)                    // 요청한 크기만큼 힙 확장
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새로운 빈 블록의 헤더 설정
    PUT(FTRP(bp), PACK(size, 0));         // 새로운 빈 블록의 푸터 설정
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더 설정

    return coalesce(bp); // 새로 확장된 힙 영역을 이전의 빈 블록과 통합
}

/* find_fit - 적당한 크기의 빈 블록을 찾아 포인터 반환 */
static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) // 힙을 순회
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 빈 블록이고 충분히 큰 경우
        {
            return bp; // 블록의 포인터 반환
        }
    }
    return NULL; // 적당한 블록을 찾지 못한 경우
}

/* place - 할당할 블록에 메모리 할당 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 분할 가능한 충분한 공간이 있는 경우
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 할당할 크기로 헤더 설정
        PUT(FTRP(bp), PACK(asize, 1)); // 할당할 크기로 푸터 설정
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 나머지 블록의 헤더 설정
        PUT(FTRP(bp), PACK(csize - asize, 0)); // 나머지 블록의 푸터 설정
    }
    else // 분할 불가능한 경우
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 전체 블록 할당
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* mm_malloc - 요청한 크기의 메모리 할당 */
void *mm_malloc(size_t size)
{
    size_t asize;      // 할당할 크기
    size_t extendsize; // 확장할 크기
    char *bp;

    if (size == 0) // 요청 크기가 0인 경우
        return NULL;

    if (size <= DSIZE) // 최소 블록 크기 설정
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 8의 배수로 크기 조정
    }

    if ((bp = find_fit(asize)) != NULL) // 적당한 빈 블록 찾기
    {
        place(bp, asize); // 찾은 블록에 메모리 할당
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);                 // 확장할 크기 결정
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) // 힙 확장
    {
        return NULL;
    }
    place(bp, asize); // 확장된 영역에 메모리 할당
    return bp;
}

/* mm_free - 메모리 해제 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr)); // 해제할 블록의 크기 가져오기
    PUT(HDRP(ptr), PACK(size, 0));     // 헤더를 빈 블록으로 설정
    PUT(FTRP(ptr), PACK(size, 0));     // 푸터를 빈 블록으로 설정
    coalesce(ptr);                     // 주변 빈 블록과 통합
}

/* mm_realloc - 메모리 재할당 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; // 기존 포인터
    void *newptr;       // 새 포인터
    size_t copySize;    // 복사할 데이터 크기

    newptr = mm_malloc(size); // 새 메모리 할당
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE; // 기존 데이터 크기 계산
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize); // 데이터 복사
    mm_free(oldptr);                  // 기존 메모리 해제
    return newptr;
}
