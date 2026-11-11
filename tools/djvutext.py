"""Extract the text layer of a DjVu file through libdjvulibre.so.21 by ctypes (the runtime library is installed, the tools and headers are not).

Usage: python3 tools/djvutext.py FILE.djvu OUTDIR  -> OUTDIR/page_NNN.txt and OUTDIR/all.txt (one "===== DJVU PAGE i =====" header per page).
Used 2026-11-11 for literature/1979-Garey-Johnson-...djvu (175 sheets of two book pages, 137,340 words of OCR), written to the .ocr.txt beside it."""
import ctypes, sys, os
L = ctypes.CDLL("libdjvulibre.so.21")
L.ddjvu_context_create.restype = ctypes.c_void_p; L.ddjvu_context_create.argtypes = [ctypes.c_char_p]
L.ddjvu_document_create_by_filename.restype = ctypes.c_void_p; L.ddjvu_document_create_by_filename.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int]
L.ddjvu_message_wait.restype = ctypes.c_void_p; L.ddjvu_message_wait.argtypes = [ctypes.c_void_p]
L.ddjvu_message_pop.argtypes = [ctypes.c_void_p]
L.ddjvu_document_job.restype = ctypes.c_void_p; L.ddjvu_document_job.argtypes = [ctypes.c_void_p]
L.ddjvu_job_status.restype = ctypes.c_int; L.ddjvu_job_status.argtypes = [ctypes.c_void_p]
L.ddjvu_document_get_pagenum.restype = ctypes.c_int; L.ddjvu_document_get_pagenum.argtypes = [ctypes.c_void_p]
L.ddjvu_document_get_pagetext.restype = ctypes.c_void_p; L.ddjvu_document_get_pagetext.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_char_p]
L.ddjvu_miniexp_release.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
L.miniexp_stringp.restype = ctypes.c_int; L.miniexp_stringp.argtypes = [ctypes.c_void_p]
L.miniexp_to_str.restype = ctypes.c_char_p; L.miniexp_to_str.argtypes = [ctypes.c_void_p]
def consp(p): return bool(p) and (p & 3) == 0
def car(p): return ctypes.cast(p, ctypes.POINTER(ctypes.c_void_p))[0]
def cdr(p): return ctypes.cast(p, ctypes.POINTER(ctypes.c_void_p))[1]
DUMMY = 2
def strings(e, out):
    """Collect every string in the s-expression, depth first."""
    if not e: return
    if consp(e):
        strings(car(e), out); strings(cdr(e), out)
    elif L.miniexp_stringp(e):
        s = L.miniexp_to_str(e); out.append(s.decode("utf-8", "replace"))
src, outdir = sys.argv[1], sys.argv[2]
ctx = L.ddjvu_context_create(b"djvutext"); doc = L.ddjvu_document_create_by_filename(ctx, src.encode(), 1)
while L.ddjvu_job_status(L.ddjvu_document_job(doc)) < 2:
    L.ddjvu_message_wait(ctx); L.ddjvu_message_pop(ctx)
n = L.ddjvu_document_get_pagenum(doc); print("pages", n)
allt = []
for i in range(n):
    while True:
        e = L.ddjvu_document_get_pagetext(doc, i, b"page")
        if e != DUMMY: break
        L.ddjvu_message_wait(ctx); L.ddjvu_message_pop(ctx)
    out = []; strings(e, out)
    if e: L.ddjvu_miniexp_release(doc, e)
    t = "\n".join(out)
    open(os.path.join(outdir, f"page_{i+1:03d}.txt"), "w").write(t); allt.append(f"\n\n===== DJVU PAGE {i+1} =====\n{t}")
open(os.path.join(outdir, "all.txt"), "w").write("".join(allt))
print("words", sum(len(t.split()) for t in allt))
