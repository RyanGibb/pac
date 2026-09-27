#!/usr/bin/env python3
"""Drop every regular file under the given paths out of the page cache.

posix_fadvise(DONTNEED) needs no privilege, only a readable file, where
/proc/sys/vm/drop_caches needs root.  It releases clean data pages not
mapped by a running process; the dentry and inode caches are untouched, so
a directory walk afterwards is still warm.  `.git` directories are skipped.

usage: evict.py <path>...
"""
import mmap, os, sys, time

PAGE = mmap.PAGESIZE


def files(p):
    if os.path.isfile(p):
        yield p
        return
    for d, dirs, fs in os.walk(p):
        dirs[:] = [x for x in dirs if x != ".git"]
        for f in fs:
            q = os.path.join(d, f)
            if os.path.isfile(q) and not os.path.islink(q):
                yield q


def main():
    t0 = time.time()
    n = size = 0
    for p in sys.argv[1:]:
        for f in files(p):
            try:
                fd = os.open(f, os.O_RDONLY)
            except OSError:
                continue
            try:
                size += os.fstat(fd).st_size
                os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)
                n += 1
            finally:
                os.close(fd)
    print(f"evicted {n} files, {size >> 20} MiB, in {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
