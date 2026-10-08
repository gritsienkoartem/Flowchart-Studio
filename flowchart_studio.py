#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FlowChart Studio — генератор блок-схем по ГОСТ 19701-90
=======================================================


Запуск:   python flowchart_studio.py                 — графическое окно
          python flowchart_studio.py prog.cpp -o out.png   — без окна
Нужен Python 3.9+. Для PNG: pip install pillow
"""
from __future__ import annotations

import argparse
import ast
import json
import math
import os
import re
import sys
import textwrap
from xml.sax.saxutils import escape as xml_escape

APP_TITLE = "FlowChart Studio — блок-схемы по ГОСТ 19701-90"


class ParseError(Exception):
    pass


# =====================================================================
#  1. Промежуточное представление (общее для всех языков)
# =====================================================================
class Stmt:
    line = None


class Simple(Stmt):
    """kind: process | io | call"""
    def __init__(self, kind, text, line=None, decl=False):
        self.kind, self.text, self.line, self.decl = kind, text, line, decl


class If(Stmt):
    def __init__(self, cond, then, other, raw="", line=None):
        self.cond, self.then, self.other, self.raw, self.line = cond, then, other, raw, line


class While(Stmt):
    def __init__(self, cond, body, raw="", line=None):
        self.cond, self.body, self.raw, self.line = cond, body, raw, line


class DoWhile(Stmt):
    def __init__(self, body, cond, raw="", line=None):
        self.body, self.cond, self.raw, self.line = body, cond, raw, line


class For(Stmt):
    def __init__(self, head, body, raw="", line=None):
        self.head, self.body, self.raw, self.line = head, body, raw, line


class Switch(Stmt):
    def __init__(self, expr, cases, default, line=None):
        # cases: [(список_значений, тело)], default: тело | None
        self.expr, self.cases, self.default, self.line = expr, cases, default, line


class Jump(Stmt):
    """kind: return | throw | break | continue"""
    def __init__(self, kind, text="", line=None):
        self.kind, self.text, self.line = kind, text, line


class Func:
    def __init__(self, name, params, body, is_main=False, line=None):
        self.name, self.params, self.body, self.is_main, self.line = name, params, body, is_main, line

    @property
    def signature(self):
        return "%s(%s)" % (self.name, ", ".join(self.params))

    @property
    def short(self):
        return re.split(r"::|\.", self.name)[-1]


class Program:
    def __init__(self, funcs, lang):
        self.funcs, self.lang = funcs, lang


# =====================================================================
#  2. Работа с текстом выражений
# =====================================================================
STR_RE = re.compile(r'''("(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*')''', re.S)


def map_code(s, fn):
    """Применяет fn только к тем кускам текста, которые не являются строковыми литералами."""
    parts = STR_RE.split(s)
    out = []
    for i, p in enumerate(parts):
        if i % 2 == 0:
            if i + 1 < len(parts):   # перед строкой — убираем префиксы $ @ f r b
                p = re.sub(r'(?<![\w$@])(?:[$@]+|[fFrRbBuU]{1,2})$', '', p)
            out.append(fn(p))
        else:
            out.append(p)
    return ''.join(out)


def top_chars(s):
    """Символы верхнего уровня (вне скобок и кавычек): (индекс, символ)."""
    depth, q, i = 0, None, 0
    while i < len(s):
        c = s[i]
        if q:
            if c == '\\':
                i += 2
                continue
            if c == q:
                q = None
        elif c in '"\'':
            q = c
        elif c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif depth == 0:
            yield i, c
        i += 1


def split_top(s, sep):
    out, start, skip = [], 0, 0
    for i, c in top_chars(s):
        if i < skip:
            continue
        if s.startswith(sep, i):
            out.append(s[start:i])
            start = skip = i + len(sep)
    out.append(s[start:])
    return out


def _wrapped(t):
    d, q, i = 0, None, 0
    while i < len(t):
        c = t[i]
        if q:
            if c == '\\':
                i += 2
                continue
            if c == q:
                q = None
        elif c in '"\'':
            q = c
        elif c == '(':
            d += 1
        elif c == ')':
            d -= 1
            if d == 0 and i < len(t) - 1:
                return False
        i += 1
    return d == 0


def unwrap(t):
    t = t.strip()
    while len(t) > 1 and t[0] == '(' and t[-1] == ')' and _wrapped(t):
        t = t[1:-1].strip()
    return t


def _args_at(t, open_idx):
    d, q, i, cur, args = 0, None, open_idx, [], []
    while i < len(t):
        c = t[i]
        if q:
            cur.append(c)
            if c == '\\' and i + 1 < len(t):
                cur.append(t[i + 1])
                i += 2
                continue
            if c == q:
                q = None
        elif c in '"\'':
            q = c
            cur.append(c)
        elif c in '([{':
            d += 1
            if d > 1:
                cur.append(c)
        elif c in ')]}':
            d -= 1
            if d == 0:
                args.append(''.join(cur))
                return i, args
            cur.append(c)
        elif c == ',' and d == 1:
            args.append(''.join(cur))
            cur = []
        else:
            cur.append(c)
        i += 1
    return None


def fix_abs(t):
    """abs(x) -> |x|."""
    for _ in range(10):
        m = re.search(r'\b(?:abs|fabs|labs|Abs)\s*\(', t)
        if not m:
            break
        res = _args_at(t, m.end() - 1)
        if not res or len(res[1]) != 1:
            break
        cl, args = res
        t = t[:m.start()] + '|' + args[0].strip() + '|' + t[cl + 1:]
    return t


def fix_calls(t):
    """pow(a,b) -> a^b."""
    t = fix_abs(t)
    for _ in range(10):
        m = re.search(r'\b(?:pow|Pow)\s*\(', t)
        if not m:
            break
        res = _args_at(t, m.end() - 1)
        if not res or len(res[1]) != 2:
            break
        cl, args = res
        a, b = [x.strip() for x in args]

        def w(s):
            return s if re.fullmatch(r'[\w.]+', s) else '(%s)' % s
        t = t[:m.start()] + w(a) + '^' + w(b) + t[cl + 1:]
    return t


TYPE_CAST_RE = re.compile(r'\(\s*(?:unsigned\s+|signed\s+)?(?:int|double|float|long|short|char|bool|decimal|byte|size_t|string)\s*\)\s*')


def norm_expr(t, lang="cpp"):
    """Выражение -> запись без синтаксиса конкретного языка."""
    t = t.strip()
    if not t:
        return t

    def code(p):
        p = TYPE_CAST_RE.sub('', p)

        def _math(m):
            n = m.group(1)
            if n in ('PI', 'pi'):
                return 'π'
            n = {'Ceiling': 'ceil'}.get(n, n)
            return n[0].lower() + n[1:]
        p = re.sub(r'\bMath\.([A-Za-z_]\w*)', _math, p)
        p = re.sub(r'\b(?:std|System|Convert|math)\s*(?:\.|::)\s*', '', p)
        p = re.sub(r'\b(?:M_PI|pi)\b', 'π', p)
        p = re.sub(r'\bnew\s+', '', p)
        if lang == 'python':
            p = re.sub(r'\bnot\b', 'НЕ', p)
            p = re.sub(r'\band\b', ' И ', p)
            p = re.sub(r'\bor\b', ' ИЛИ ', p)
            p = p.replace('//', ' div ').replace('**', '^')
            p = re.sub(r'\bTrue\b', 'истина', p)
            p = re.sub(r'\bFalse\b', 'ложь', p)
            p = re.sub(r'\bNone\b', 'пусто', p)
        else:
            p = p.replace('&&', ' И ').replace('||', ' ИЛИ ')
            p = re.sub(r'!(?!=)', 'НЕ ', p)
            p = re.sub(r'\btrue\b', 'истина', p)
            p = re.sub(r'\bfalse\b', 'ложь', p)
            p = re.sub(r'\b(?:null|nullptr|NULL)\b', 'пусто', p)
        p = re.sub(r'(?<![=!<>])==(?!=)', '=', p)
        p = p.replace('!=', '≠')
        p = re.sub(r'%(?!=)', ' mod ', p)
        p = re.sub(r'\b[Ss]qrt\s*\(', '√(', p)
        p = re.sub(r'\s*(<=|>=|≠|(?<![<>=\-!])=(?![=>])|(?<![-<>])[<>](?![<>=]))\s*', r' \1 ', p)
        p = re.sub(r',(?=\S)', ', ', p)
        p = re.sub(r'(?<=[\w)\]])(?<![0-9.][eE])\s*([+\-*/])\s*(?=[\w(\[√|.π])', r' \1 ', p)
        return p
    t = map_code(t, code)
    t = fix_calls(t)
    if lang == 'python':
        t = re.sub(r"'([^'\"\\]*)'", r'"\1"', t)
    t = re.sub(r'\s{2,}', ' ', t).strip()
    return t


def norm_cond(raw, lang="cpp"):
    return norm_expr(unwrap(raw), lang)


def norm_assign(t):
    """i++ -> i = i + 1;  x += 2 -> x = x + 2."""
    t = t.strip()
    m = re.fullmatch(r'(\+\+|--)\s*([\w.\[\]]+)', t)
    if m:
        return '%s = %s %s 1' % (m.group(2), m.group(2), '+' if m.group(1) == '++' else '-')
    m = re.fullmatch(r'([\w.\[\]]+)\s*(\+\+|--)', t)
    if m:
        return '%s = %s %s 1' % (m.group(1), m.group(1), '+' if m.group(2) == '++' else '-')
    for i, c in top_chars(t):
        if c != '=':
            continue
        if t[i + 1:i + 2] == '=':
            continue
        pair, prv = t[max(i - 2, 0):i], t[i - 1:i]
        if pair in ('<<', '>>', '//', '**'):
            op = pair
        elif prv in ('<', '>', '!', '='):
            continue
        elif prv and prv in '+-*/%&|^':
            op = prv
        else:
            return t
        lhs, rhs = t[:i - len(op)].strip(), t[i + 1:].strip()
        if not lhs or not rhs:
            return t
        if op in ('*', '/', '%', '//', '**') and re.search(r'[-+]', rhs) \
                and not re.fullmatch(r'-?[\w.]+', rhs) and not (rhs[0] == '(' and _wrapped(rhs)):
            rhs = '(%s)' % rhs
        return '%s = %s %s %s' % (lhs, lhs, op, rhs)
    return t


KW_NOT_TYPE = {'return', 'else', 'delete', 'throw', 'new', 'goto', 'case', 'using', 'typedef', 'namespace',
               'do', 'break', 'continue', 'sizeof', 'yield', 'await', 'in', 'is', 'as', 'not', 'and', 'or',
               'print', 'del', 'elif', 'import'}

DECL_RE = re.compile(r'''^
    (?:(?:const|static|readonly|volatile|constexpr|register|extern|final|mutable|inline)\s+)*
    (?:(?:unsigned|signed|long|short)\s+)*
    (?P<type>[A-Za-z_]\w*(?:(?:::|\.)[A-Za-z_]\w*)*(?:\s*<[^;=()]*?>)?(?:\s*\[[\s,]*\])*)
    (?:\s*[*&]+\s*|\s+)
    (?P<rest>[A-Za-z_]\w*\s*(?:=(?!=)|;|,|\[|\(|$).*)$''', re.X | re.S)


def strip_decl(t):
    """'int a = 5, b;' -> (True, 'a = 5'). Объявления без значения отбрасываются."""
    t = t.strip().rstrip(';').strip()
    m = DECL_RE.match(t)
    if not m:
        return False, t
    base = re.split(r'::|\.', m.group('type'))[0]
    if base in KW_NOT_TYPE:
        return False, t
    keep = []
    for p in split_top(m.group('rest'), ','):
        p = p.strip().lstrip('*& ')
        if not p:
            continue
        mm = re.match(r'^(\w+)\s*(?:\[[^\]]*\])*\s*=(?!=)\s*(.*)$', p, re.S)
        if mm:
            keep.append('%s = %s' % (mm.group(1), mm.group(2).strip()))
            continue
        mm = re.match(r'^(\w+)\s*\((.*)\)$', p, re.S)
        if mm:
            keep.append('%s = %s' % (mm.group(1), mm.group(2).strip()))
    return True, ', '.join(keep)


def norm_stmt(t, lang, allow_decl=True):
    t = t.strip().rstrip(';').strip()
    if lang != 'python' and allow_decl:
        isd, rest = strip_decl(t)
        if isd:
            t = rest
    pieces = split_top(t, ',') if lang != 'python' else [t]
    return ', '.join(norm_expr(norm_assign(p.strip()), lang) for p in pieces if p.strip())


# ------------------------- ввод / вывод ------------------------------
def _is_str(s):
    return bool(re.fullmatch(r'"(?:\\.|[^"\\])*"', s.strip(), re.S))


def _add_lit(parts, lit):
    lit = lit.replace('\\n', '').replace('\\t', ' ').replace('{{', '{').replace('}}', '}')
    if lit.strip() != '':
        parts.append('"%s"' % lit)


def interp_parts(body):
    """Тело интерполированной строки ($"..{x}.." / f'..{x}..') -> список частей."""
    parts, pos = [], 0
    for m in re.finditer(r'\{\{|\}\}|\{([^{}]+)\}', body):
        if m.group(1) is None:
            continue
        _add_lit(parts, body[pos:m.start()])
        pos = m.end()
        expr = split_top(split_top(m.group(1), ':')[0], ',')[0]
        parts.append(expr.strip())
    _add_lit(parts, body[pos:])
    return parts


PRINTF_RE = re.compile(r'%(?:%|[-+ #0]*\d*(?:\.\d+)?(?:hh|h|ll|l|z|L)?[diouxXfFeEgGcsp])')
NETFMT_RE = re.compile(r'\{(\d+)(?:[,:][^}]*)?\}')


def fmt_parts(fmt, args, kind):
    body = fmt.strip()[1:-1]
    rx = PRINTF_RE if kind == 'c' else NETFMT_RE
    parts, pos, ai = [], 0, 0
    for m in rx.finditer(body):
        if m.group(0) == '%%':
            continue
        _add_lit(parts, body[pos:m.start()])
        pos = m.end()
        idx = ai if kind == 'c' else int(m.group(1))
        ai += 1
        if idx < len(args):
            parts.append(args[idx])
    _add_lit(parts, body[pos:])
    return parts


def _expand_arg(a):
    a = a.strip()
    m = re.fullmatch(r'\$@?"(.*)"', a, re.S) or re.fullmatch(r'[fF]["\'](.*)["\']', a, re.S)
    if m:
        return interp_parts(m.group(1))
    return [a]


def try_output(t, lang):
    """None — это не вывод; список — части вывода (может быть пустым)."""
    m = re.match(r'^(?:std::)?cout\s*<<\s*(.*)$', t, re.S)
    if m:
        skip = re.compile(r'^(?:std::)?(?:endl|flush|fixed|boolalpha|left|right)$|^(?:std::)?set\w+\(.*\)$|^["\']\\n["\']$')
        return [p.strip() for p in split_top(m.group(1), '<<') if p.strip() and not skip.match(p.strip())]
    m = re.match(r'^(?:std::)?w?printf\s*\((.*)\)$', t, re.S)
    if m:
        args = [a.strip() for a in split_top(m.group(1), ',')]
        return fmt_parts(args[0], args[1:], 'c') if _is_str(args[0]) else args
    m = re.match(r'^(?:std::)?puts\s*\((.*)\)$', t, re.S)
    if m:
        return fmt_parts(m.group(1), [], 'c') if _is_str(m.group(1)) else [m.group(1)]
    m = re.match(r'^(?:System\.)?Console\.(?:Out\.)?Write(?:Line)?\s*\((.*)\)$', t, re.S) \
        or re.match(r'^MessageBox\.Show\s*\((.*)\)$', t, re.S)
    if m:
        inner = m.group(1).strip()
        if not inner:
            return []
        args = [a.strip() for a in split_top(inner, ',')]
        if args[0].startswith('$'):
            return _expand_arg(args[0])
        if _is_str(args[0]) and len(args) > 1 and NETFMT_RE.search(args[0]):
            return fmt_parts(args[0], args[1:], 'net')
        if _is_str(args[0]) and len(args) == 1:
            return [args[0].replace('\\n', '')]
        return args
    if lang == 'python':
        m = re.match(r'^print\s*\((.*)\)$', t, re.S)
        if m:
            parts = []
            for a in split_top(m.group(1), ','):
                a = a.strip()
                if not a or re.match(r'^(?:sep|end|file|flush)\s*=(?!=)', a):
                    continue
                parts.extend(_expand_arg(a))
            return parts
    return None


def try_input(t, lang):
    """None — не ввод; [] — «пауза» (пропускаем); список переменных."""
    m = re.match(r'^(?:std::)?cin\s*>>\s*(.*)$', t, re.S)
    if m:
        return [v.strip() for v in split_top(m.group(1), '>>') if v.strip()]
    m = re.match(r'^(?:std::)?getline\s*\(\s*(?:std::)?cin\s*,\s*(.+)\)$', t, re.S)
    if m:
        return [m.group(1).strip()]
    m = re.match(r'^(?:scanf|scanf_s)\s*\((.*)\)$', t, re.S)
    if m:
        args = [a.strip().lstrip('&') for a in split_top(m.group(1), ',')][1:]
        return args
    if re.fullmatch(r'(?:_?getch\s*\(\)|getchar\s*\(\)|(?:std::)?cin\.get\s*\(\)|system\s*\(.*\)|'
                    r'(?:std::)?cin\.ignore\s*\(.*\)|(?:std::)?cin\.tie\s*\(.*\)|(?:std::)?cout\.tie\s*\(.*\)|'
                    r'(?:std::)?ios(?:_base)?::sync_with_stdio\s*\(.*\)|srand\s*\(.*\)|'
                    r'Console\.(?:ReadKey|Clear)\s*\(.*\)|Console\.ReadLine\s*\(\)|Console\.Read\s*\(\))', t):
        return []
    if lang != 'python' and re.search(r'\bConsole\.Read(?:Line|Key)?\s*\(', t):
        pos = [i for i, c in top_chars(t) if c == '=' and t[i + 1:i + 2] != '=' and t[i - 1:i] not in '<>!=']
        if pos:
            lhs = t[:pos[0]].strip()
            isd, rest = strip_decl(lhs + ' = 0')
            lhs = rest.split(' = ')[0] if isd else lhs
            return [lhs]
        mo = re.search(r'\bout\s+(?:\w+\s+)?(\w+)', t)
        if mo:
            return [mo.group(1)]
        return []
    if lang == 'python' and re.search(r'\binput\s*\(', t):
        pos = [i for i, c in top_chars(t) if c == '=' and t[i + 1:i + 2] != '=' and t[i - 1:i] not in '<>!=']
        if pos:
            return [split_top(t[:pos[0]], ':')[0].strip()]
        return []
    return None


def _find_ternary(rhs):
    q = None
    for i, c in top_chars(rhs):
        if c == '?' and rhs[i + 1:i + 2] not in ('?', '.', '[') and rhs[i - 1:i] != '?':
            q = i
            break
    if q is None:
        return None
    for j, c in top_chars(rhs):
        if j > q and c == ':' and rhs[j + 1:j + 2] != ':' and rhs[j - 1:j] != ':':
            return rhs[:q], rhs[q + 1:j], rhs[j + 1:]
    return None


def translate_simple(text, lang):
    """Один оператор исходника -> список узлов схемы."""
    t = re.sub(r'\s+', ' ', text.strip().rstrip(';')).strip()
    if not t:
        return []
    out = try_output(t, lang)
    if out is not None:
        out = [p for p in out if p.strip() and not re.fullmatch(r'["\']\s*["\']', p.strip())]
        if not out:
            return []
        txt = ', '.join(norm_expr(p, lang) for p in out)
        if len(out) == 1 and re.fullmatch(r'"[^"]*"', txt):
            txt = txt[1:-1]                      # одиночная строка — без кавычек
        return [Simple('io', txt)]
    inp = try_input(t, lang)
    if inp is not None:
        return [Simple('io', ', '.join(inp))] if inp else []
    decl_flag = False
    if lang != 'python':
        isd, rest = strip_decl(t)
        if isd:
            if not rest:
                return []
            t = rest
            decl_flag = True
        # a = cond ? x : y   ->  ветвление
        pos = [i for i, c in top_chars(t) if c == '=' and t[i + 1:i + 2] != '=' and t[i - 1:i] not in '<>!=+-*/%&|^']
        if pos:
            lhs, rhs = t[:pos[0]].strip(), t[pos[0] + 1:].strip()
            tern = _find_ternary(rhs)
            if tern:
                c, a, b = tern
                return [If(norm_cond(c, lang),
                           translate_simple('%s = %s' % (lhs, a.strip()), lang),
                           translate_simple('%s = %s' % (lhs, b.strip()), lang), raw=c)]
    res = norm_stmt(t, lang, allow_decl=False)
    return [Simple('process', res, decl=decl_flag)] if res else []


# =====================================================================
#  3. Разбор C++ / C#
# =====================================================================
TOKEN_RE = re.compile(r'''
    (?P<nl>\n)
   |(?P<pp>^[ \t]*\#[^\n]*(?:\\\n[^\n]*)*)
   |(?P<ws>[ \t\r\f\v]+)
   |(?P<cm>//[^\n]*|/\*.*?\*/)
   |(?P<str>@"(?:[^"]|"")*"|\$@?"(?:\\.|[^"\\\n])*"|"(?:\\.|[^"\\\n])*"|'(?:\\.|[^'\\\n])*')
   |(?P<num>\d[\w.]*)
   |(?P<id>[A-Za-z_]\w*)
   |(?P<op><<=|>>=|=>|->|::|\+\+|--|&&|\|\||==|!=|<=|>=|<<|>>|[-+*/%&|^]=|\S)
''', re.X | re.M | re.S)


class Tok:
    __slots__ = ('kind', 'text', 'line', 'sp')

    def __init__(self, kind, text, line, sp):
        self.kind, self.text, self.line, self.sp = kind, text, line, sp


def tokenize(src):
    toks, line, sp = [], 1, False
    for m in TOKEN_RE.finditer(src):
        k, txt = m.lastgroup, m.group()
        if k == 'nl':
            line += 1
            sp = True
        elif k in ('ws', 'cm', 'pp'):
            line += txt.count('\n')
            sp = True
        else:
            toks.append(Tok(k, txt, line, sp))
            line += txt.count('\n')
            sp = False
    return toks


CONTROL = {'if', 'while', 'for', 'foreach', 'switch', 'catch', 'using', 'lock', 'return', 'sizeof', 'typeof',
           'nameof', 'do', 'else', 'new', 'throw', 'fixed', 'checked', 'unchecked', 'decltype', 'alignof'}
CONTAINERS = ('namespace', 'class', 'struct', 'interface', 'enum', 'union', 'record')


def split_params(s):
    out, d, cur = [], 0, []
    for c in s:
        if c in '<([{':
            d += 1
        elif c in '>)]}':
            d -= 1
        if c == ',' and d == 0:
            out.append(''.join(cur))
            cur = []
        else:
            cur.append(c)
    out.append(''.join(cur))
    return [p.strip() for p in out if p.strip()]


class CParser:
    def __init__(self, src, lang):
        self.lang = lang
        self.toks = tokenize(src)
        self.n = len(self.toks)
        self.i = 0
        self.funcs = []
        self.stray = []

    # ---------- утилиты ----------
    def tx(self, k=0):
        """Текст токена (для строк и чисел — служебная заглушка, чтобы не путать с ключевыми словами)."""
        j = self.i + k
        if 0 <= j < self.n:
            t = self.toks[j]
            return t.text if t.kind in ('op', 'id') else '\0'
        return ''

    def eof(self):
        return self.i >= self.n

    def cur_line(self):
        return self.toks[min(self.i, self.n - 1)].line if self.n else 0

    def match(self, j):
        pairs = {'(': ')', '[': ']', '{': '}'}
        op = self.toks[j].text
        cl = pairs[op]
        d = 0
        for k in range(j, self.n):
            t = self.toks[k]
            if t.kind == 'op':
                if t.text == op:
                    d += 1
                elif t.text == cl:
                    d -= 1
                    if d == 0:
                        return k
        return None

    def join(self, a, b):
        out = []
        for k in range(a, b):
            t = self.toks[k]
            if k > a and t.sp:
                out.append(' ')
            out.append(t.text)
        return ''.join(out)

    def paren(self):
        if self.tx() != '(':
            return self.i, self.i
        q = self.match(self.i)
        if q is None:
            q = self.n
        a = self.i + 1
        self.i = q + 1
        return a, q

    def gather(self):
        a, d = self.i, 0
        while self.i < self.n:
            t = self.toks[self.i]
            if t.kind == 'op':
                if t.text in ('(', '[', '{'):
                    d += 1
                elif t.text in (')', ']', '}'):
                    if d == 0:
                        break
                    d -= 1
                elif t.text == ';' and d == 0:
                    b = self.i
                    self.i += 1
                    return a, b
            self.i += 1
        return a, self.i

    # ---------- функции ----------
    def first_paren(self, i):
        j = i
        while j < self.n:
            x = self.toks[j]
            if x.kind == 'op':
                if x.text in ('=', ';', '{', '}'):
                    return -1
                if x.text == '(':
                    return j if j > i else -1
            j += 1
        return -1

    def name_index(self, p):
        j = p - 1
        if j >= 0 and self.toks[j].text == '>':
            d = 0
            while j >= 0:
                if self.toks[j].text == '>':
                    d += 1
                elif self.toks[j].text == '<':
                    d -= 1
                    if d == 0:
                        j -= 1
                        break
                j -= 1
        return j

    def is_function_at(self, i):
        p = self.first_paren(i)
        if p < 0:
            return False
        ni = self.name_index(p)
        if ni < i or self.toks[ni].kind != 'id' or self.toks[ni].text in CONTROL:
            return False
        q = self.match(p)
        if q is None:
            return False
        k = q + 1
        while k < self.n:
            x = self.toks[k]
            if x.kind == 'op':
                if x.text in ('{', '=>'):
                    return True
                if x.text in (';', '=', '}'):
                    return False
                if x.text == '(':
                    e = self.match(k)
                    if e is None:
                        return False
                    k = e
            k += 1
        return False

    def parse_function(self):
        line = self.cur_line()
        p = self.first_paren(self.i)
        ni = self.name_index(p)
        k = ni
        while k >= 2 and self.toks[k - 1].text in ('::', '.') and self.toks[k - 2].kind == 'id':
            k -= 2
        full = ''.join(t.text for t in self.toks[k:ni + 1])
        q = self.match(p)
        params = []
        for prm in split_params(self.join(p + 1, q)):
            prm = prm.split('=')[0].strip()
            m = re.search(r'([A-Za-z_]\w*)\s*(?:\[[^\]]*\])*\s*$', prm)
            if m and prm != 'void':
                params.append(m.group(1))
        self.i = q + 1
        while not self.eof() and self.tx() not in ('{', '=>'):
            if self.tx() == '(':
                e = self.match(self.i)
                self.i = (e if e is not None else self.n) + 1
            else:
                self.i += 1
        if self.tx() == '=>':
            self.i += 1
            a, b = self.gather()
            text = self.join(a, b)
            nodes = translate_simple(text, self.lang) if try_output(text.strip(), self.lang) is not None \
                else [Jump('return', norm_expr(text, self.lang), line)]
            body = nodes
        else:
            body = self.parse_block()
        f = Func(full, params, body, is_main=(full.split('::')[-1].lower() == 'main'), line=line)
        self.funcs.append(f)

    # ---------- верхний уровень ----------
    def container_at(self, i):
        j = i
        while j < self.n and self.toks[j].kind == 'id':
            if self.toks[j].text in CONTAINERS:
                return j
            j += 1
        return None

    def skip_decl(self):
        while not self.eof():
            t = self.toks[self.i]
            if t.kind == 'op' and t.text == ';':
                self.i += 1
                return
            if t.kind == 'op' and t.text == '}':
                return
            if t.kind == 'op' and t.text == '{':
                e = self.match(self.i)
                self.i = (e if e is not None else self.n) + 1
                if self.tx() in ('=', ';'):
                    continue
                return
            self.i += 1

    def parse_items(self, level):
        while not self.eof():
            t = self.toks[self.i]
            x = t.text
            if t.kind == 'op':
                if x == '}':
                    if level > 0:
                        return
                    self.i += 1
                    continue
                if x == ';':
                    self.i += 1
                    continue
                if x == '[':
                    e = self.match(self.i)
                    self.i = (e if e is not None else self.n) + 1
                    continue
            if t.kind == 'id':
                if x in ('public', 'private', 'protected') and self.tx(1) == ':':
                    self.i += 2
                    continue
                if x == 'using' and self.tx(1) != '(':
                    while not self.eof() and self.tx() != ';':
                        self.i += 1
                    self.i += 1
                    continue
                if x == 'template' and self.tx(1) == '<':
                    self.i += 1
                    d = 0
                    while not self.eof():
                        if self.tx() == '<':
                            d += 1
                        elif self.tx() == '>':
                            d -= 1
                            if d == 0:
                                self.i += 1
                                break
                        self.i += 1
                    continue
                j = self.container_at(self.i)
                if j is not None:
                    kw = self.toks[j].text
                    self.i = j + 1
                    while not self.eof() and self.tx() not in ('{', ';'):
                        self.i += 1
                    if self.tx() == ';':
                        self.i += 1
                        continue
                    if kw == 'enum':
                        e = self.match(self.i)
                        self.i = (e if e is not None else self.n) + 1
                        if self.tx() == ';':
                            self.i += 1
                        continue
                    self.i += 1
                    self.parse_items(level + 1)
                    if self.tx() == '}':
                        self.i += 1
                    if self.tx() == ';':
                        self.i += 1
                    continue
            if self.is_function_at(self.i):
                self.parse_function()
                continue
            before = self.i
            if self.lang == 'csharp' and level == 0:
                self.stray.extend(self.parse_statement())
            else:
                self.skip_decl()
            if self.i == before:
                self.i += 1

    def parse(self):
        self.parse_items(0)
        main_body = self.stray
        if not self.funcs and not main_body:      # просто набор операторов (C++ без main)
            self.i = 0
            while not self.eof():
                b = self.i
                main_body.extend(self.parse_statement())
                if self.i == b:
                    self.i += 1
        funcs = self.funcs
        if main_body:
            funcs = [Func('Программа', [], main_body, True)] + [f for f in funcs if not f.is_main] \
                if not any(f.is_main for f in funcs) else funcs
        funcs.sort(key=lambda f: 0 if f.is_main else 1)
        return funcs

    # ---------- операторы ----------
    def parse_block(self):
        out = []
        if self.tx() == '{':
            self.i += 1
        while not self.eof() and self.tx() != '}':
            b = self.i
            out.extend(self.parse_statement())
            if self.i == b:
                self.i += 1
        if self.tx() == '}':
            self.i += 1
        return out

    def parse_body(self):
        if self.tx() == '{':
            return self.parse_block()
        return self.parse_statement()

    def parse_statement(self):
        if self.eof():
            return []
        t = self.toks[self.i]
        x, line = t.text, t.line
        if t.kind == 'op':
            if x == '{':
                return self.parse_block()
            if x == ';':
                self.i += 1
                return []
        if t.kind == 'id':
            if x == 'if':
                return [self.p_if()]
            if x == 'while':
                self.i += 1
                a, b = self.paren()
                raw = self.join(a, b)
                return [While(norm_cond(raw, self.lang), self.parse_body(), raw, line)]
            if x == 'do':
                self.i += 1
                body = self.parse_body()
                if self.tx() == 'while':
                    self.i += 1
                a, b = self.paren()
                if self.tx() == ';':
                    self.i += 1
                raw = self.join(a, b)
                return [DoWhile(body, norm_cond(raw, self.lang), raw, line)]
            if x == 'for':
                return self.p_for()
            if x == 'foreach':
                return self.p_foreach()
            if x == 'switch':
                return self.p_switch()
            if x in ('return', 'throw'):
                self.i += 1
                a, b = self.gather()
                return [Jump(x, norm_expr(self.join(a, b), self.lang), line)]
            if x in ('break', 'continue'):
                self.i += 1
                if self.tx() == ';':
                    self.i += 1
                return [Jump(x, '', line)]
            if x == 'try':
                return self.p_try()
            if x == 'else':
                self.i += 1
                return []
            if x == 'goto':
                self.i += 1
                a, b = self.gather()
                return [Simple('process', 'Переход к метке ' + self.join(a, b), line)]
            if x in ('using', 'lock', 'unsafe', 'checked', 'unchecked', 'fixed'):
                self.i += 1
                if self.tx() == '(':
                    self.paren()
                    return self.parse_body()
                if x == 'using' and self.tx() == 'namespace' or self.tx() == ';':
                    self.gather()
                    return []
                if self.tx() == '{':
                    return self.parse_block()
                return self.parse_statement()
            if self.tx(1) == ':' and self.tx(2) != ':' and x not in ('case', 'default', 'public', 'private', 'protected'):
                self.i += 2               # метка goto
                return []
            if self.is_function_at(self.i):
                self.parse_function()     # локальная функция (C#)
                return []
        a, b = self.gather()
        nodes = translate_simple(self.join(a, b), self.lang)
        for n in nodes:
            n.line = line
        return nodes

    def p_if(self):
        line = self.cur_line()
        self.i += 1
        a, b = self.paren()
        raw = self.join(a, b)
        then = self.parse_body()
        other = []
        if self.tx() == 'else':
            self.i += 1
            other = self.parse_body()
        return If(norm_cond(raw, self.lang), then, other, raw, line)

    def p_for(self):
        line = self.cur_line()
        self.i += 1
        a, b = self.paren()
        head = self.join(a, b)
        body = self.parse_body()
        parts = split_top(head, ';')
        if len(parts) >= 3:
            init, cond, it = [p.strip() for p in parts[:3]]
            if not (init or cond or it):
                return [While('истина', body, 'true', line)]
            pieces = []
            if init:
                pieces.append(norm_stmt(init, self.lang))
            if cond:
                pieces.append(norm_cond(cond, self.lang))
            if it:
                pieces.append(norm_stmt(it, self.lang))
            return [For(', '.join(p for p in pieces if p), body, cond, line)]
        colon = [i for i, c in top_chars(head) if c == ':' and head[i + 1:i + 2] != ':' and head[i - 1:i] != ':']
        if colon:
            lhs, rng = head[:colon[0]], head[colon[0] + 1:]
            m = re.search(r'\[([^\]]*)\]', lhs)
            ids = re.findall(r'[A-Za-z_]\w*', lhs)
            var = m.group(1).strip() if m else (ids[-1] if ids else lhs.strip())
            return [For('для каждого %s из %s' % (var, norm_expr(rng, self.lang)), body, '', line)]
        return [For(norm_expr(head, self.lang), body, '', line)]

    def p_foreach(self):
        line = self.cur_line()
        self.i += 1
        a, b = self.paren()
        head = self.join(a, b)
        body = self.parse_body()
        m = re.match(r'^(?:.*\s)?(\w+)\s+in\s+(.+)$', head, re.S)
        if m:
            txt = 'для каждого %s из %s' % (m.group(1), norm_expr(m.group(2), self.lang))
        else:
            txt = norm_expr(head, self.lang)
        return [For(txt, body, '', line)]

    def p_try(self):
        self.i += 1
        body = self.parse_body()
        while self.tx() == 'catch':
            self.i += 1
            if self.tx() == '(':
                self.paren()
            if self.tx() == 'when':
                self.i += 1
                self.paren()
            self.parse_body()
        extra = []
        if self.tx() == 'finally':
            self.i += 1
            extra = self.parse_body()
        return body + extra

    def at_label(self):
        return self.tx() == 'case' or (self.tx() == 'default' and self.tx(1) == ':')

    def p_switch(self):
        line = self.cur_line()
        self.i += 1
        a, b = self.paren()
        expr = norm_cond(self.join(a, b), self.lang)
        if self.tx() == '{':
            self.i += 1
        cases, default = [], None
        while not self.eof() and self.tx() != '}':
            labels, is_def = [], False
            while self.at_label():
                if self.tx() == 'case':
                    self.i += 1
                    s, d = self.i, 0
                    while not self.eof():
                        x = self.tx()
                        if x in ('(', '[', '{'):
                            d += 1
                        elif x in (')', ']', '}'):
                            d -= 1
                        elif x == ':' and d == 0:
                            break
                        self.i += 1
                    labels.append(norm_expr(self.join(s, self.i), self.lang))
                    self.i += 1
                else:
                    self.i += 2
                    is_def = True
            if not labels and not is_def:
                b0 = self.i
                self.parse_statement()
                if self.i == b0:
                    self.i += 1
                continue
            body = []
            while not self.eof() and self.tx() != '}' and not self.at_label():
                b0 = self.i
                body.extend(self.parse_statement())
                if self.i == b0:
                    self.i += 1
            if body and isinstance(body[-1], Jump) and body[-1].kind == 'break':
                body.pop()
            if is_def:
                default = (default or []) + body
            else:
                cases.append((labels, body))
        if self.tx() == '}':
            self.i += 1
        return [Switch(expr, cases, default, line)]


# =====================================================================
#  4. Разбор Python (через ast)
# =====================================================================
class PyConv:
    def __init__(self):
        self.funcs = []

    def body(self, stmts):
        out = []
        for s in stmts:
            out.extend(self.stmt(s))
        return out

    def _range_head(self, target, it):
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == 'range' \
                and not it.keywords and 1 <= len(it.args) <= 3:
            a = [norm_expr(ast.unparse(x), 'python') for x in it.args]
            if len(a) == 1:
                start, stop, step = '0', a[0], '1'
            elif len(a) == 2:
                start, stop, step = a[0], a[1], '1'
            else:
                start, stop, step = a
            neg = step.startswith('-')
            cmp_ = '>' if neg else '<'
            upd = '%s = %s %s %s' % (target, target, '-' if neg else '+', step.lstrip('-'))
            return '%s = %s, %s %s %s, %s' % (target, start, target, cmp_, stop, upd)
        return 'для каждого %s из %s' % (target, norm_expr(ast.unparse(it), 'python'))

    def stmt(self, n):
        line = getattr(n, 'lineno', None)
        U = ast.unparse
        if isinstance(n, ast.If):
            raw = U(n.test)
            return [If(norm_cond(raw, 'python'), self.body(n.body), self.body(n.orelse), raw, line)]
        if isinstance(n, ast.While):
            raw = U(n.test)
            return [While(norm_cond(raw, 'python'), self.body(n.body), raw, line)]
        if isinstance(n, (ast.For, ast.AsyncFor)):
            target = norm_expr(U(n.target), 'python')
            return [For(self._range_head(target, n.iter), self.body(n.body), '', line)]
        if isinstance(n, ast.Return):
            return [Jump('return', norm_expr(U(n.value), 'python') if n.value else '', line)]
        if isinstance(n, ast.Raise):
            return [Jump('throw', norm_expr(U(n.exc), 'python') if n.exc else '', line)]
        if isinstance(n, ast.Break):
            return [Jump('break', '', line)]
        if isinstance(n, ast.Continue):
            return [Jump('continue', '', line)]
        if isinstance(n, (ast.Pass, ast.Import, ast.ImportFrom, ast.Global, ast.Nonlocal)):
            return []
        if isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant) and isinstance(n.value.value, str):
            return []
        if isinstance(n, ast.Try):
            return self.body(n.body) + self.body(n.finalbody)
        if isinstance(n, (ast.With, ast.AsyncWith)):
            return self.body(n.body)
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            self.add_func(n)
            return []
        if isinstance(n, ast.ClassDef):
            for b in n.body:
                if isinstance(b, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    self.add_func(b, prefix=n.name + '.')
            return []
        if isinstance(n, ast.Assert):
            return [Simple('process', 'Проверить: ' + norm_expr(U(n.test), 'python'), line)]
        if hasattr(ast, 'Match') and isinstance(n, ast.Match):
            expr = norm_expr(U(n.subject), 'python')
            cases, default = [], None
            for c in n.cases:
                body = self.body(c.body)
                pat = c.pattern
                if isinstance(pat, ast.MatchAs) and pat.pattern is None:
                    default = (default or []) + body
                else:
                    cases.append(([norm_expr(x, 'python') for x in U(pat).split(' | ')], body))
            return [Switch(expr, cases, default, line)]
        if isinstance(n, ast.Assign) and isinstance(n.value, ast.IfExp) and len(n.targets) == 1:
            tgt = U(n.targets[0])
            raw = U(n.value.test)
            mk = lambda v: translate_simple('%s = %s' % (tgt, U(v)), 'python')
            return [If(norm_cond(raw, 'python'), mk(n.value.body), mk(n.value.orelse), raw, line)]
        if isinstance(n, ast.AnnAssign):
            if n.value is None:
                return []
            text = '%s = %s' % (U(n.target), U(n.value))
        else:
            text = U(n)
        nodes = translate_simple(text, 'python')
        for x in nodes:
            x.line = line
        return nodes

    def add_func(self, n, prefix=''):
        a = n.args
        names = [x.arg for x in getattr(a, 'posonlyargs', [])] + [x.arg for x in a.args]
        if a.vararg:
            names.append('*' + a.vararg.arg)
        names += [x.arg for x in a.kwonlyargs]
        if a.kwarg:
            names.append('**' + a.kwarg.arg)
        if names and names[0] in ('self', 'cls') and prefix:
            names = names[1:]
        self.funcs.append(Func(prefix + n.name, names, self.body(n.body), False, n.lineno))


def parse_python(src):
    try:
        tree = ast.parse(src)
    except SyntaxError as e:
        raise ParseError('Синтаксическая ошибка Python (строка %s): %s' % (e.lineno, e.msg))
    conv = PyConv()
    main_body = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            conv.add_func(node)
        elif isinstance(node, ast.ClassDef):
            conv.stmt(node)
        elif isinstance(node, ast.If) and re.fullmatch(r"__name__\s*==\s*['\"]__main__['\"]", ast.unparse(node.test)):
            main_body.extend(conv.body(node.body))
        else:
            main_body.extend(conv.stmt(node))
    funcs = conv.funcs
    if len(main_body) == 1 and isinstance(main_body[0], Simple) and re.fullmatch(r'main\(\s*\)', main_body[0].text):
        for f in funcs:
            if f.name == 'main':
                f.is_main = True
        main_body = []
    if main_body:
        funcs = [Func('Программа', [], main_body, True)] + funcs
    funcs.sort(key=lambda f: 0 if f.is_main else 1)
    return funcs


# =====================================================================
#  5. Общий вход: определение языка, разбор, пометка вызовов методов
# =====================================================================
LANG_NAMES = {'cpp': 'C++', 'csharp': 'C#', 'python': 'Python'}
LANG_BY_NAME = {'C++': 'cpp', 'C#': 'csharp', 'Python': 'python', 'cpp': 'cpp', 'csharp': 'csharp',
                'python': 'python', 'c++': 'cpp', 'c#': 'csharp', 'cs': 'csharp', 'py': 'python'}


def detect_lang(src):
    s = src
    py = len(re.findall(r'^\s*(?:def |import |from \S+ import |elif |print\()', s, re.M)) + \
        len(re.findall(r':\s*$', s, re.M))
    cs = len(re.findall(r'Console\.|using System|namespace |\bstring\[\]|\bforeach\b|\bvar\b|\.Length\b|\$"', s))
    cp = len(re.findall(r'#include|std::|\bcout\b|\bcin\b|\bprintf\b|using namespace|\bnullptr\b|\bvector<', s))
    if py > cs + cp and not re.search(r'[;{]\s*$', s, re.M):
        return 'python'
    if cs >= cp and cs > 0:
        return 'csharp'
    if cp > 0:
        return 'cpp'
    if py > 0 and not re.search(r'[;{}]\s*$', s, re.M):
        return 'python'
    return 'cpp'


def _walk(stmts, fn):
    for s in stmts:
        fn(s)
        if isinstance(s, If):
            _walk(s.then, fn)
            _walk(s.other, fn)
        elif isinstance(s, (While, DoWhile, For)):
            _walk(s.body, fn)
        elif isinstance(s, Switch):
            for _, b in s.cases:
                _walk(b, fn)
            if s.default:
                _walk(s.default, fn)


def mark_calls(funcs):
    names = {f.short for f in funcs}
    if not names:
        return

    def fn(s):
        if isinstance(s, Simple) and s.kind == 'process':
            for nm in names:
                if re.search(r'(?<![\w.])%s\s*\(' % re.escape(nm), s.text):
                    s.kind = 'call'
                    break
    for f in funcs:
        _walk(f.body, fn)


def parse_code(src, lang=None):
    lang = LANG_BY_NAME.get(lang) if lang and lang not in ('auto', 'Авто') else None
    lang = lang or detect_lang(src)
    if not src.strip():
        raise ParseError('Код пустой.')
    if lang == 'python':
        funcs = parse_python(src)
    else:
        try:
            funcs = CParser(src, lang).parse()
        except RecursionError:
            raise ParseError('Слишком сложная вложенность в коде.')
    if not funcs:
        raise ParseError('Не найдено ни одной инструкции или метода для построения схемы.')
    mark_calls(funcs)
    return Program(funcs, lang)


# =====================================================================
#  6. Раскладка блок-схемы (по ГОСТ 19701-90 и методичке)
# =====================================================================
GAP = 30          # длина соединительной линии между блоками
CW = 7.4          # ширина символа (px) для оценки размеров блоков
LH = 17           # высота строки текста
FS = 13           # размер шрифта
MARGIN = 30


def wrap(text, width):
    out = []
    for part in str(text).split('\n'):
        part = re.sub(r'\s+', ' ', part).strip()
        if part:
            out.extend(textwrap.wrap(part, width=width, break_long_words=True, break_on_hyphens=False) or [part])
    return out or ['']


def size_box(kind, text):
    """-> (w, h, lines)"""
    if kind == 'decision':
        lines = wrap(text, 22)
        tw, th = max(len(l) for l in lines) * CW, len(lines) * LH
        h = max(58, th * 2 + 16)
        w = max(120, tw / (1 - th / h) + 26)
    elif kind == 'terminal':
        lines = wrap(text, 26)
        tw, th = max(len(l) for l in lines) * CW, len(lines) * LH
        w, h = max(96, tw + 46), max(34, th + 16)
    elif kind == 'loop':
        lines = wrap(text, 36)
        tw, th = max(len(l) for l in lines) * CW, len(lines) * LH
        w, h = max(120, tw + 28 + 44), max(42, th + 22)
    elif kind == 'io':
        lines = wrap(text, 42)
        tw, th = max(len(l) for l in lines) * CW, len(lines) * LH
        w, h = max(110, tw + 28 + 36), max(38, th + 18)
    elif kind == 'call':
        lines = wrap(text, 30)
        tw, th = max(len(l) for l in lines) * CW, len(lines) * LH
        w, h = max(110, tw + 28 + 26), max(38, th + 18)
    else:
        lines = wrap(text, 46)
        tw, th = max(len(l) for l in lines) * CW, len(lines) * LH
        w, h = max(100, tw + 28), max(38, th + 18)
    return w, h, lines


class Lay:
    """Фрагмент схемы. Ось x=0, верх y=0; вход в (0,0), выход из (0,h)."""
    __slots__ = ('prims', 'left', 'right', 'h', 'term', 'jumps')

    def __init__(self):
        self.prims, self.left, self.right, self.h, self.term = [], 0.0, 0.0, 0.0, False
        self.jumps = []       # неразрешённые break/continue: (вид, Frame, x, y)

    @property
    def empty(self):
        return not self.prims and self.h == 0

    def place(self, sub, dx, dy):
        self.prims.extend(shift(p, dx, dy) for p in sub.prims)
        self.jumps.extend((k, f, x + dx, y + dy) for k, f, x, y in sub.jumps)


def shift(p, dx, dy):
    k = p[0]
    if k == 'line':
        return ('line', [(x + dx, y + dy) for x, y in p[1]], p[2])
    if k == 'box':
        return (k, p[1], p[2] + dx, p[3] + dy) + p[4:]
    if k == 'label':
        return (k, p[1] + dx, p[2] + dy, p[3])
    if k == 'conn':
        return (k, p[1] + dx, p[2] + dy) + p[3:]
    return p


def box_lay(kind, text):
    w, h, lines = size_box(kind, text)
    L = Lay()
    L.prims.append(('box', kind, 0, h / 2, w, h, lines))
    L.left = L.right = w / 2
    L.h = h
    return L


def vstack(items, gap=GAP):
    L, y, first = Lay(), 0.0, True
    for c in items:
        if c.empty:
            continue
        if not first:
            L.prims.append(('line', [(0, y), (0, y + gap)], True))
            y += gap
        first = False
        L.place(c, 0, y)
        L.left, L.right = max(L.left, c.left), max(L.right, c.right)
        y += c.h
        if c.term:
            L.term = True
            break
    L.h = y
    return L


class Frame:
    def __init__(self, kind):
        self.kind, self.break_label, self.cont_label = kind, None, None


class Ctx:
    LETTERS = 'АБВГДЕЖИКЛМНПРСТУФХЦЧШЭЮЯ'

    def __init__(self, opts=None):
        opts = opts or {}
        self.stack, self.n = [], 0
        if opts.get('labels') == 'yn':
            self.yes, self.no = 'Да', 'Нет'
        else:
            self.yes, self.no = '+', '-'

    def new_label(self):
        lab = self.LETTERS[self.n] if self.n < len(self.LETTERS) else str(self.n + 1)
        self.n += 1
        return lab

    def push(self, kind):
        self.stack.append(Frame(kind))

    def pop(self):
        return self.stack.pop()


def lab_pos(text, x, y):
    return ('label', x + 3 * len(text), y, text)


def merge_simple(stmts):
    """Подряд идущие обычные операторы — в один блок (по строке на оператор); каждое объявление — отдельный блок."""
    out = []
    for s in stmts:
        if isinstance(s, Simple) and s.kind == 'process' and not s.decl and out \
                and isinstance(out[-1], Simple) and out[-1].kind == 'process' and not out[-1].decl:
            out[-1] = Simple('process', out[-1].text + '\n' + s.text, out[-1].line)
        else:
            out.append(s)
    return out


def find_frame(kind, ctx):
    if kind == 'break':
        return ctx.stack[-1] if ctx.stack else None
    return next((f for f in reversed(ctx.stack) if f.kind == 'loop'), None)


def lay_block(stmts, ctx):
    return vstack([lay_stmt(s, ctx) for s in merge_simple(stmts)])


def lay_stmt(s, ctx):
    if isinstance(s, Simple):
        return box_lay(s.kind, s.text)
    if isinstance(s, If):
        return lay_if(s, ctx)
    if isinstance(s, While):
        if s.cond.strip().lower() in ('истина', '1'):
            return lay_forever(s.body, ctx)
        return lay_while(s.cond, s.body, ctx, 'decision')
    if isinstance(s, For):
        return lay_while(s.head, s.body, ctx, 'loop')
    if isinstance(s, DoWhile):
        return lay_dowhile(s, ctx)
    if isinstance(s, Switch):
        return lay_switch(s, ctx)
    if isinstance(s, Jump):
        return lay_jump(s, ctx)
    return Lay()


def lay_jump(j, ctx):
    if j.kind in ('return', 'throw'):
        parts = []
        if j.kind == 'throw':
            parts.append(box_lay('process', 'Ошибка: ' + j.text if j.text else 'Ошибка'))
        elif j.text:
            parts.append(box_lay('process', 'Возврат: ' + j.text))
        parts.append(box_lay('terminal', 'конец'))
        L = vstack(parts)
        L.term = True
        return L
    fr = find_frame(j.kind, ctx)
    if fr is None:                                  # break/continue вне цикла
        L = box_lay('process', 'Выход' if j.kind == 'break' else 'Следующая итерация')
        L.term = True
        return L
    L = Lay()
    L.prims.append(('line', [(0, 0), (0, 10)], False))
    L.jumps.append((j.kind, fr, 0, 10))             # линия будет проведена в объемлющем цикле / switch
    L.h = 10
    L.term = True
    return L


def lay_if(st, ctx):
    dw, dh, dl = size_box('decision', st.cond)
    direct = None                     # if (...) break; / continue;  -> линия прямо из ромба
    if len(st.then) == 1 and isinstance(st.then[0], Jump) and st.then[0].kind in ('break', 'continue'):
        fr0 = find_frame(st.then[0].kind, ctx)
        if fr0 is not None:
            direct = (st.then[0].kind, fr0)
    if direct:
        T = Lay()
        T.term = True
    else:
        T = lay_block(st.then, ctx)
    E = lay_block(st.other, ctx)
    L = Lay()
    L.prims.append(('box', 'decision', 0, dh / 2, dw, dh, dl))
    if direct:
        L.jumps.append((direct[0], direct[1], dw / 2, dh / 2))
    y0 = dh + GAP
    xr = max(dw / 2 + 34, E.right + GAP + T.left)
    r = 5
    t_reach, e_reach = not T.term, not E.term
    start = (dw / 2, dh / 2)
    L.prims.append(lab_pos(ctx.yes, dw / 2 + 8, dh / 2 - 11))
    L.prims.append(lab_pos(ctx.no, 10, dh + 12))
    if T.h > 0:
        L.place(T, xr, y0)
        L.prims.append(('line', [start, (xr, dh / 2), (xr, y0)], True))
    if E.h > 0:
        n_e = len(L.jumps)
        L.place(E, 0, y0)
        L.prims.append(('line', [(0, dh), (0, y0)], True))
        if T.h > 0:
            _reroute_below(L, n_e, y0 + T.h + 10)
    L.left = max(dw / 2, E.left if E.h > 0 else 0)
    L.right = max(dw / 2, xr + (T.right if T.h > 0 else 0)) + 4
    if direct:
        L.right = dw / 2 + 4
    if not t_reach and not e_reach:
        L.term = True
        L.h = y0 + max(T.h, E.h)
        return L
    if e_reach and not t_reach:            # ветвь «+» завершается (return/break), слияния нет
        L.h = y0 + max(E.h, T.h) if T.h > 0 else (y0 + E.h if E.h > 0 else dh)
        e_end = y0 + E.h if E.h > 0 else dh
        if L.h > e_end:
            L.prims.append(('line', [(0, e_end), (0, L.h)], False))
        return L
    ym = max(y0 + T.h, y0 + E.h) + GAP * 0.6
    L.prims.append(('conn', 0, ym, r, '', False))            # соединитель
    if T.h > 0:
        L.prims.append(('line', [(xr, y0 + T.h), (xr, ym), (r, ym)], True))
    else:
        L.prims.append(('line', [start, (xr, dh / 2), (xr, ym), (r, ym)], True))
    if e_reach:
        if E.h > 0:
            L.prims.append(('line', [(0, y0 + E.h), (0, ym - r)], True))
        else:
            L.prims.append(('line', [(0, dh), (0, ym - r)], True))
    L.h = ym + r
    return L


def _reroute_below(L, start, ysafe):
    """Прыжки, начатые на оси под боковой веткой: сначала вниз ниже соседних блоков, затем вбок."""
    for n in range(start, len(L.jumps)):
        k, f, x, y = L.jumps[n]
        if ysafe > y:
            L.prims.append(('line', [(x, y), (x, ysafe)], False))
            L.jumps[n] = (k, f, x, ysafe)


def _take(L, fr):
    """Забирает из L разрешаемые в этой конструкции прыжки."""
    mine = [(k, x, y) for k, f, x, y in L.jumps if f is fr]
    L.jumps = [j for j in L.jumps if j[1] is not fr]
    return ([(x, y) for k, x, y in mine if k == 'continue'],
            [(x, y) for k, x, y in mine if k == 'break'])


def lay_while(cond, body, ctx, shape='decision'):
    """while / for: условие сверху, тело вниз по оси, возврат слева, выход справа и вниз."""
    ctx.push('loop')
    B = lay_block(body, ctx)
    fr = ctx.pop()
    dw, dh, dl = size_box(shape, cond)
    L = Lay()
    cy = dh / 2
    L.prims.append(('box', shape, 0, cy, dw, dh, dl))
    L.prims.append(lab_pos(ctx.yes, 10, dh + 12))
    L.prims.append(lab_pos(ctx.no, dw / 2 + 12, cy - 11))
    if B.h > 0:
        y0 = dh + GAP
        L.prims.append(('line', [(0, dh), (0, y0)], True))
        L.place(B, 0, y0)
        yB = y0 + B.h
    else:
        yB = dh
    conts, brks = _take(L, fr)
    ybk = yB + GAP * 0.6
    xl = -(max(dw / 2, B.left) + 30)
    xc = max(dw / 2, B.right) + 14
    xe = max(dw / 2, B.right) + 30
    y_exit = ybk + GAP * 0.7
    if B.h == 0:
        L.prims.append(('line', [(0, dh), (0, ybk)], False))
    elif not B.term:
        L.prims.append(('line', [(0, yB), (0, ybk)], False))
    if B.h == 0 or not B.term or conts:
        L.prims.append(('line', [(0, ybk), (xl, ybk), (xl, cy), (-dw / 2, cy)], True))
    if conts:                                             # continue -> в линию возврата
        for px, py in conts:
            L.prims.append(('line', [(px, py), (xc, py)], False))
        L.prims.append(('line', [(xc, min(y for _, y in conts)), (xc, ybk), (0, ybk)], False))
        L.prims.append(('conn', 0, ybk, 3, '', True))
    L.prims.append(('line', [(dw / 2, cy), (xe, cy), (xe, y_exit), (0, y_exit)], False))
    for px, py in brks:                                   # break -> в линию выхода
        L.prims.append(('line', [(px, py), (xe, py)], False))
        L.prims.append(('conn', xe, py, 3, '', True))
    L.left = max(-xl, dw / 2) + 4
    L.right = xe + 4
    L.h = y_exit
    return L


def lay_forever(body, ctx):
    """Цикл без условия (while(true)): точка слияния сверху, выход только через break."""
    ctx.push('loop')
    B = lay_block(body, ctx)
    fr = ctx.pop()
    L = Lay()
    jg = 24
    L.prims.append(('conn', 0, 0, 3, '', True))
    L.prims.append(('line', [(0, 0), (0, jg)], True))
    if B.h > 0:
        L.place(B, 0, jg)
    yB = jg + B.h
    conts, brks = _take(L, fr)
    ybk = yB + GAP * 0.6
    wl, wr = max(B.left, 40), max(B.right, 40)
    xl, xc, xb = -(wl + 30), wr + 14, wr + 30
    if not B.term:
        L.prims.append(('line', [(0, yB), (0, ybk)], False))
    if not B.term or conts:
        L.prims.append(('line', [(0, ybk), (xl, ybk), (xl, 0), (-3, 0)], True))
    if conts:
        for px, py in conts:
            L.prims.append(('line', [(px, py), (xc, py)], False))
        L.prims.append(('line', [(xc, min(y for _, y in conts)), (xc, ybk), (0, ybk)], False))
        L.prims.append(('conn', 0, ybk, 3, '', True))
    L.left = -xl + 4
    L.right = wr + 4
    if brks:
        y_exit = ybk + GAP * 0.7
        for px, py in brks:
            L.prims.append(('line', [(px, py), (xb, py)], False))
        L.prims.append(('line', [(xb, min(y for _, y in brks)), (xb, y_exit), (0, y_exit)], False))
        L.right = xb + 4
        L.h = y_exit
    else:
        L.term = True
        L.h = ybk
    return L


def lay_dowhile(st, ctx):
    ctx.push('loop')
    B = lay_block(st.body, ctx)
    fr = ctx.pop()
    dw, dh, dl = size_box('decision', st.cond)
    L = Lay()
    jg = 24
    L.prims.append(('conn', 0, 0, 3, '', True))
    conts, brks = [], []
    if B.h > 0:
        L.prims.append(('line', [(0, 0), (0, jg)], True))
        L.place(B, 0, jg)
        conts, brks = _take(L, fr)
        y = jg + B.h
        ytop = y + GAP
        L.prims.append(('line', [(0, y), (0, ytop)], True))
    else:
        ytop = jg
        L.prims.append(('line', [(0, 0), (0, ytop)], True))
    cy, bot = ytop + dh / 2, ytop + dh
    L.prims.append(('box', 'decision', 0, cy, dw, dh, dl))
    xb = -(max(B.left, dw / 2) + 34)
    L.prims.append(('line', [(-dw / 2, cy), (xb, cy), (xb, 0), (-3, 0)], True))
    L.prims.append(lab_pos(ctx.yes, -dw / 2 - 14, cy - 11))
    L.prims.append(lab_pos(ctx.no, 10, bot + 12))
    L.left = -xb + 4
    L.right = max(B.right, dw / 2) + 4
    lane_c = max(B.right, dw / 2) + 22
    if conts:                                                    # continue -> к проверке условия
        yj = ytop - 12
        for px, py in conts:
            L.prims.append(('line', [(px, py), (lane_c, py)], False))
        L.prims.append(('line', [(lane_c, min(y for _, y in conts)), (lane_c, yj), (0, yj)], False))
        L.prims.append(('conn', 0, yj, 3, '', True))
        L.right = max(L.right, lane_c + 4)
    if brks:                                                     # break -> выход из цикла
        lane_b = lane_c + 16
        ym = bot + 18
        for px, py in brks:
            L.prims.append(('line', [(px, py), (lane_b, py)], False))
        L.prims.append(('line', [(lane_b, min(y for _, y in brks)), (lane_b, ym), (0, ym)], False))
        L.prims.append(('line', [(0, bot), (0, ym)], False))
        L.prims.append(('conn', 0, ym, 3, '', True))
        L.right = max(L.right, lane_b + 4)
        L.h = ym
    else:
        L.h = bot
    return L


def lay_switch(st, ctx):
    ctx.push('switch')
    bodies = [(labs, lay_block(b, ctx)) for labs, b in st.cases]
    D = lay_block(st.default, ctx) if st.default is not None else Lay()
    fr = ctx.pop()
    if not bodies:
        return D
    dims = [size_box('decision', ' или '.join('%s = %s' % (st.expr, l) for l in labs)) for labs, _ in bodies]
    maxdw = max(d[0] for d in dims)
    nz = [B for _, B in bodies if B.h > 0]
    bl = max((B.left for B in nz), default=0)
    br = max((B.right for B in nz), default=0)
    xr = maxdw / 2 + 34 + bl
    if D.h > 0:
        xr = max(xr, D.right + GAP + bl)
    xt = max(xr + br + 26, maxdw / 2 + 34)
    L = Lay()
    prev_bot, prev_join, joins, max_bb = None, None, [], 0.0
    for i, ((labs, B), (dw, dh, dl)) in enumerate(zip(bodies, dims)):
        top = 0.0 if i == 0 else prev_bot + GAP
        cy = top + dh / 2
        if prev_join is not None:
            cy = max(cy, prev_join + 14)
        top = cy - dh / 2
        if i > 0:
            L.prims.append(('line', [(0, prev_bot), (0, top)], True))
            L.prims.append(lab_pos(ctx.no, 10, prev_bot + 12))
        L.prims.append(('box', 'decision', 0, cy, dw, dh, dl))
        L.prims.append(lab_pos(ctx.yes, dw / 2 + 8, cy - 11))
        if B.h > 0:
            by = cy + GAP
            L.prims.append(('line', [(dw / 2, cy), (xr, cy), (xr, by)], True))
            L.place(B, xr, by)
            bb = by + B.h
            max_bb = max(max_bb, bb)
            if not B.term:
                jy = bb + GAP * 0.5
                L.prims.append(('line', [(xr, bb), (xr, jy), (xt, jy)], False))
                joins.append(jy)
                prev_join = jy
            else:
                prev_join = bb
        else:
            L.prims.append(('line', [(dw / 2, cy), (xt, cy)], False))
            joins.append(cy)
            prev_join = cy
        prev_bot = top + dh
    last_bot = prev_bot
    L.prims.append(lab_pos(ctx.no, 10, last_bot + 12))
    if D.h > 0:
        dtop = last_bot + GAP
        L.prims.append(('line', [(0, last_bot), (0, dtop)], True))
        n_d = len(L.jumps)
        L.place(D, 0, dtop)
        dbot = dtop + D.h
        _reroute_below(L, n_d, max(max_bb, dbot) + 10)
    else:
        dbot = last_bot
    _, brks = _take(L, fr)                      # break внутри case (не в конце) -> к слиянию
    for px, py in brks:
        L.prims.append(('line', [(px, py), (xt, py)], False))
        joins.append(py)
        prev_join = max(prev_join or 0, py)
    d_reach = not D.term
    if not joins and not d_reach:
        L.term = True
        L.h = max(dbot, prev_join or 0)
        L.left, L.right = max(maxdw / 2, D.left), xt + 4
        return L
    ym = max(dbot, prev_join or 0) + GAP * 0.7
    r = 5
    if d_reach:
        L.prims.append(('line', [(0, dbot), (0, ym - r)], True))
    if joins:
        L.prims.append(('line', [(xt, min(joins)), (xt, ym), (r, ym)], True))
        for jy in joins:
            L.prims.append(('conn', xt, jy, 3, '', True))
    L.prims.append(('conn', 0, ym, r, '', False))
    L.h = ym + r
    L.left = max(maxdw / 2, D.left if D.h > 0 else 0)
    L.right = xt + 4
    return L


def lay_function(f, ctx):
    body = list(f.body)
    if body and isinstance(body[-1], Jump) and body[-1].kind == 'return':
        j = body.pop()
        if j.text and not f.is_main:
            body.append(Simple('process', 'Возврат: ' + j.text))
    start = box_lay('terminal', 'начало' if f.is_main else f.signature)
    lay = lay_block(body, ctx)
    items = [start, lay]
    if not lay.term:
        items.append(box_lay('terminal', 'конец'))
    return vstack(items)


# =====================================================================
#  7. Геометрия и «плоская» сцена (общая для Tk, SVG и PNG)
# =====================================================================
def shape_geom(kind, cx, cy, w, h):
    x0, x1, y0, y1 = cx - w / 2, cx + w / 2, cy - h / 2, cy + h / 2
    extra = []
    rect = [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]
    if kind == 'io':
        s = 16
        poly = [(x0 + s, y0), (x1, y0), (x1 - s, y1), (x0, y1)]
    elif kind == 'decision':
        poly = [(cx, y0), (x1, cy), (cx, y1), (x0, cy)]
    elif kind == 'loop':
        s = 20
        poly = [(x0 + s, y0), (x1 - s, y0), (x1, cy), (x1 - s, y1), (x0 + s, y1), (x0, cy)]
    elif kind == 'call':
        poly = rect
        extra = [[(x0 + 10, y0), (x0 + 10, y1)], [(x1 - 10, y0), (x1 - 10, y1)]]
    elif kind == 'terminal':
        r = h / 2
        poly = [(x1 - r + r * math.cos(-math.pi / 2 + math.pi * k / 18), cy + r * math.sin(-math.pi / 2 + math.pi * k / 18))
                for k in range(19)]
        poly += [(x0 + r + r * math.cos(math.pi / 2 + math.pi * k / 18), cy + r * math.sin(math.pi / 2 + math.pi * k / 18))
                 for k in range(19)]
    else:
        poly = rect
    return poly, extra


def arrow_head(pts):
    (x0, y0), (x1, y1) = pts[-2], pts[-1]
    dx, dy = x1 - x0, y1 - y0
    l = math.hypot(dx, dy) or 1.0
    ux, uy = dx / l, dy / l
    bx, by = x1 - 10 * ux, y1 - 10 * uy
    return [(x1, y1), (bx - 4.5 * uy, by + 4.5 * ux), (bx + 4.5 * uy, by - 4.5 * ux)]


class Scene:
    def __init__(self, w, h, items):
        self.w, self.h, self.items = w, h, items


INK, PAPER = '#000000', '#ffffff'


def flatten(prims, ox, oy, lines, shapes, texts):
    for p in prims:
        k = p[0]
        if k == 'box':
            _, kind, cx, cy, w, h, tl = p
            cx, cy = cx + ox, cy + oy
            poly, extra = shape_geom(kind, cx, cy, w, h)
            shapes.append(('poly', poly, PAPER, INK, 1.5))
            for e in extra:
                shapes.append(('line', e, INK, 1.5))
            n = len(tl)
            for i, l in enumerate(tl):
                texts.append(('text', cx, cy + (i - (n - 1) / 2) * LH, l))
        elif k == 'line':
            pts = [(x + ox, y + oy) for x, y in p[1]]
            lines.append(('line', pts, INK, 1.3))
            if p[2]:
                lines.append(('poly', arrow_head(pts), INK, INK, 1))
        elif k == 'label':
            texts.append(('text', p[1] + ox, p[2] + oy, p[3]))
        elif k == 'conn':
            _, cx, cy, r, txt, filled = p
            shapes.append(('circle', cx + ox, cy + oy, r, INK if filled else PAPER, INK))
            if txt:
                texts.append(('text', cx + ox, cy + oy, txt))


def build_scene(prog, opts=None):
    charts = []
    for f in prog.funcs:
        lay = lay_function(f, Ctx(opts))
        charts.append(lay)
    L, S, T = [], [], []
    x, pad, total_h = MARGIN, 34, 0
    for lay in charts:
        inner = lay.left + lay.right
        width = inner + 2 * pad
        ox = x + pad + lay.left
        oy = MARGIN + pad
        flatten(lay.prims, ox, oy, L, S, T)
        fb = oy + lay.h + pad
        total_h = max(total_h, fb)
        x += width + MARGIN
    return Scene(x, total_h + MARGIN / 2, L + S + T)


# ------------------------------ SVG -----------------------------------
def _pts(pts):
    return ' '.join('%.1f,%.1f' % p for p in pts)


def to_svg(scene):
    o = ['<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" viewBox="0 0 %d %d" '
         'font-family="Arial, Helvetica, DejaVu Sans, sans-serif" font-size="%d">' % (scene.w, scene.h, scene.w, scene.h, FS),
         '<rect width="100%" height="100%" fill="#ffffff"/>']
    for it in scene.items:
        k = it[0]
        if k == 'poly':
            _, pts, fill, stroke, w = it
            o.append('<polygon points="%s" fill="%s" stroke="%s" stroke-width="%s" stroke-linejoin="round"/>'
                     % (_pts(pts), fill or 'none', stroke, w))
        elif k == 'line':
            o.append('<polyline points="%s" fill="none" stroke="%s" stroke-width="%s" stroke-linejoin="round"/>'
                     % (_pts(it[1]), it[2], it[3]))
        elif k == 'circle':
            o.append('<circle cx="%.1f" cy="%.1f" r="%s" fill="%s" stroke="%s" stroke-width="1.5"/>' % it[1:])
        elif k == 'text':
            o.append('<text x="%.1f" y="%.1f" text-anchor="middle" dominant-baseline="central" fill="#000">%s</text>'
                     % (it[1], it[2], xml_escape(it[3])))
    o.append('</svg>')
    return '\n'.join(o)


# ------------------------------ PNG (Pillow) ---------------------------
FONT_CANDIDATES = [
    'C:/Windows/Fonts/arial.ttf', 'C:/Windows/Fonts/segoeui.ttf', 'C:/Windows/Fonts/calibri.ttf',
    '/Library/Fonts/Arial.ttf', '/System/Library/Fonts/Supplemental/Arial.ttf',
    '/System/Library/Fonts/Supplemental/Arial Unicode.ttf',
    '/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf', '/usr/share/fonts/dejavu/DejaVuSans.ttf',
    '/usr/share/fonts/TTF/DejaVuSans.ttf', '/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf',
    '/usr/share/fonts/liberation/LiberationSans-Regular.ttf', '/usr/share/fonts/truetype/freefont/FreeSans.ttf',
    'arial.ttf', 'DejaVuSans.ttf', 'LiberationSans-Regular.ttf']


def load_font(size):
    from PIL import ImageFont
    for path in FONT_CANDIDATES:
        try:
            return ImageFont.truetype(path, size)
        except Exception:
            continue
    raise RuntimeError('Не найден TrueType-шрифт с кириллицей для PNG. Используйте экспорт в SVG.')


def to_png(scene, path, scale=2):
    try:
        from PIL import Image, ImageDraw
    except ImportError:
        raise RuntimeError('Для PNG нужен Pillow:  pip install pillow  (или используйте SVG)')
    font = load_font(int(FS * scale))
    img = Image.new('RGB', (int(scene.w * scale), int(scene.h * scale)), 'white')
    d = ImageDraw.Draw(img)
    sc = lambda pts: [(x * scale, y * scale) for x, y in pts]
    for it in scene.items:
        k = it[0]
        if k == 'poly':
            _, pts, fill, stroke, w = it
            p = sc(pts)
            if fill:
                d.polygon(p, fill=fill)
            d.line(p + [p[0]], fill=stroke, width=max(1, int(w * scale)), joint='curve')
        elif k == 'line':
            d.line(sc(it[1]), fill=it[2], width=max(1, int(it[3] * scale)), joint='curve')
        elif k == 'circle':
            _, cx, cy, r, fill, stroke = it
            d.ellipse([(cx - r) * scale, (cy - r) * scale, (cx + r) * scale, (cy + r) * scale],
                      fill=fill, outline=stroke, width=max(1, int(1.5 * scale)))
        elif k == 'text':
            d.text((it[1] * scale, it[2] * scale), it[3], fill='black', font=font, anchor='mm')
    img.save(path)


# =====================================================================
#  8. Автоанализ кода (недочёты, которые заметит проверяющая команда)
# =====================================================================
def _has_exit(stmts):
    found = []

    def fn(s):
        if isinstance(s, Jump) and s.kind in ('break', 'return', 'throw'):
            found.append(s)
    _walk(stmts, fn)
    return bool(found)


def analyze(prog):
    """-> список (строка|None, вид, текст)."""
    issues = []
    lang = prog.lang

    def add(line, kind, text):
        issues.append((line, kind, text))

    called = set()
    all_text = []

    def collect(s):
        if isinstance(s, Simple):
            all_text.append(s.text)
        elif isinstance(s, Jump):
            all_text.append(s.text)
        for attr in ('cond', 'head', 'expr'):
            if hasattr(s, attr):
                all_text.append(str(getattr(s, attr)))
    for f in prog.funcs:
        _walk(f.body, collect)

    def check(stmts, depth):
        for idx, s in enumerate(stmts):
            if isinstance(s, Jump) and s.kind in ('return', 'break', 'continue', 'throw') and idx < len(stmts) - 1:
                nxt = stmts[idx + 1]
                add(getattr(nxt, 'line', None), 'Ошибка', 'Недостижимый код после «%s».' % {
                    'return': 'return', 'break': 'break', 'continue': 'continue', 'throw': 'throw'}[s.kind])
            if isinstance(s, Simple):
                if re.search(r'(?:/|div|mod)\s*0(?![\d.])', s.text):
                    add(s.line, 'Ошибка', 'Деление на ноль: «%s».' % s.text)
            if isinstance(s, (If, While, DoWhile)) and lang != 'python' and \
                    re.search(r'(?<![=!<>])=(?![=])', re.sub(r'"[^"]*"', '', s.raw or '')):
                add(s.line, 'Ошибка', 'Присваивание «=» в условии — вероятно, нужно сравнение «==».')
            if isinstance(s, If):
                if not s.then and not s.other:
                    add(s.line, 'Недочёт', 'Пустое ветвление: обе ветви ничего не делают.')
                elif not s.then:
                    add(s.line, 'Недочёт', 'Пустая ветвь «+»: лучше инвертировать условие.')
                if depth >= 3:
                    add(s.line, 'Недочёт', 'Глубокая вложенность условий (%d) — схема трудно читается.' % (depth + 1))
                check(s.then, depth + 1)
                check(s.other, depth if (len(s.other) == 1 and isinstance(s.other[0], If)) else depth + 1)
            elif isinstance(s, (While, For, DoWhile)):
                body = s.body
                if not body:
                    add(s.line, 'Недочёт', 'Пустое тело цикла.')
                cond = getattr(s, 'cond', '')
                if isinstance(s, (While, DoWhile)) and cond.strip().lower() in ('истина', '1') and not _has_exit(body):
                    add(s.line, 'Ошибка', 'Бесконечный цикл: нет break/return внутри тела.')
                if isinstance(s, For) and s.raw and re.search(r'<=\s*\w+\s*(?:\.Length|\.size\(\)|\.Count)', s.raw):
                    add(s.line, 'Ошибка', 'Возможен выход за границы массива (<= длины вместо <).')
                if depth >= 3:
                    add(s.line, 'Недочёт', 'Глубокая вложенность циклов/условий.')
                check(body, depth + 1)
            elif isinstance(s, Switch):
                if s.default is None:
                    add(s.line, 'Недочёт', 'В switch/match нет ветки по умолчанию (default).')
                for _, b in s.cases:
                    check(b, depth + 1)
                    if not b:
                        add(s.line, 'Недочёт', 'Пустая ветвь case.')
                check(s.default or [], depth + 1)

    for f in prog.funcs:
        check(f.body, 0)
        if len(f.body) > 40:
            add(f.line, 'Предложение', 'Метод «%s» слишком длинный — вынесите часть в подпрограммы.' % f.name)
    joined = '\n'.join(all_text)
    for f in prog.funcs:
        if not f.is_main and not re.search(r'(?<![\w.])%s\s*\(' % re.escape(f.short), joined):
            add(f.line, 'Предложение', 'Метод «%s» нигде не вызывается.' % f.name)
    issues.sort(key=lambda x: (x[0] is None, x[0] or 0))
    return issues


# =====================================================================
#  9. Проект четырёх команд: сохранение, сборка в один файл
# =====================================================================
NOTE_KINDS = ['Ошибка', 'Недочёт', 'Предложение', 'Оформление (ГОСТ)']


def new_project():
    return {'teams': [{'lang': 'Авто', 'code': ''} for _ in range(4)], 'notes': []}


def lang_of(team):
    l = LANG_BY_NAME.get(team.get('lang', ''))
    return l or (detect_lang(team['code']) if team.get('code', '').strip() else 'cpp')


def author_name(a):
    return 'Авто-анализ' if not a else 'Команда %d' % a


def merge_project(teams, notes):
    """Все коды команд + замечания к ним -> один текстовый файл (замечания — комментариями)."""
    out = []
    stats = {}
    for n in notes:
        stats[n['kind']] = stats.get(n['kind'], 0) + 1
    out.append('// ' + '=' * 70)
    out.append('// ОБЪЕДИНЁННЫЙ ФАЙЛ: коды 4 команд и замечания перекрёстной проверки')
    out.append('// Замечаний всего: %d  (%s)' % (len(notes), ', '.join('%s: %d' % kv for kv in stats.items()) or '—'))
    out.append('// Формат замечания:  >>> [кто -> вид] текст')
    out.append('// ' + '=' * 70)
    for i, t in enumerate(teams, 1):
        c = '#' if lang_of(t) == 'python' else '//'
        out.append('')
        out.append('%s %s' % (c, '=' * 70))
        out.append('%s КОМАНДА %d   (язык: %s)' % (c, i, LANG_NAMES[lang_of(t)]))
        out.append('%s %s' % (c, '=' * 70))
        mine = [n for n in notes if n['target'] == i]
        by_line, free = {}, []
        for n in mine:
            try:
                by_line.setdefault(int(str(n['line']).strip()), []).append(n)
            except (ValueError, TypeError):
                free.append(n)
        lines = t.get('code', '').splitlines()
        for no, text in enumerate(lines, 1):
            out.append(text)
            ind = re.match(r'\s*', text).group(0)
            for n in by_line.get(no, []):
                out.append('%s%s >>> [%s -> %s] %s' % (ind, c, author_name(n['author']), n['kind'], n['text']))
        extra = free + [n for ln, lst in by_line.items() if ln > len(lines) or ln < 1 for n in lst]
        if extra:
            out.append('')
            out.append('%s --- Замечания без привязки к строке ---' % c)
            for n in extra:
                out.append('%s >>> [%s -> %s] %s' % (c, author_name(n['author']), n['kind'], n['text']))
    return '\n'.join(out) + '\n'


def save_project(path, proj):
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(proj, f, ensure_ascii=False, indent=2)


def load_project(path):
    with open(path, encoding='utf-8') as f:
        p = json.load(f)
    base = new_project()
    base['teams'] = (p.get('teams', []) + base['teams'])[:4]
    for t in base['teams']:
        t.setdefault('lang', 'Авто')
        t.setdefault('code', '')
    base['notes'] = p.get('notes', [])
    return base


def read_text_file(path):
    for enc in ('utf-8-sig', 'cp1251', 'utf-8'):
        try:
            with open(path, encoding=enc) as f:
                return f.read()
        except UnicodeDecodeError:
            continue
    with open(path, encoding='utf-8', errors='replace') as f:
        return f.read()


# =====================================================================
#  10. Примеры
# =====================================================================
SAMPLES = {
'C++': r'''#include <iostream>
#include <cmath>
using namespace std;

// Метод: сумма нечётных чисел до n
int sumOdd(int n) {
    int s = 0;
    for (int i = 1; i <= n; i++) {
        if (i % 2 == 0)
            continue;
        s += i;
    }
    return s;
}

int main() {
    double a, b, c;
    cin >> a >> b >> c;
    double d = b * b - 4 * a * c;
    if (d >= 0) {
        double ds = sqrt(d);
        cout << (-b + ds) / (2 * a) << " " << (-b - ds) / (2 * a) << endl;
    } else {
        cout << "Корней нет" << endl;
    }
    int n;
    cin >> n;
    int k = 0;
    while (k < n) {
        k++;
        if (k > 100)
            break;
    }
    switch (n) {
        case 1:
            cout << "Один" << endl;
            break;
        case 2:
        case 3:
            cout << "Два или три" << endl;
            break;
        default:
            cout << sumOdd(n) << endl;
    }
    do {
        n--;
    } while (n > 0);
    return 0;
}
''',
'C#': r'''using System;

class Program
{
    static int Factorial(int n)
    {
        int result = 1;
        for (int i = 2; i <= n; i++)
        {
            result *= i;
        }
        return result;
    }

    static void Main()
    {
        int n = int.Parse(Console.ReadLine());
        int sum = 0;
        int i = 0;
        while (i < n)
        {
            i++;
            if (i % 2 == 0)
                continue;
            sum += i;
            if (sum > 100)
                break;
        }
        Console.WriteLine($"Сумма нечётных: {sum}");
        switch (n)
        {
            case 1:
                Console.WriteLine("Один");
                break;
            case 2:
            case 3:
                Console.WriteLine("Два или три");
                break;
            default:
                Console.WriteLine(Factorial(n));
                break;
        }
        string res = n > 5 ? "много" : "мало";
        Console.WriteLine(res);
    }
}
''',
'Python': r'''def classify(x):
    if x < 0:
        return "отрицательное"
    elif x == 0:
        return "ноль"
    return "положительное"


def main():
    n = int(input())
    total = 0
    for i in range(1, n + 1):
        if i % 2 == 0:
            continue
        total += i
    while total > 10:
        total -= 3
        if total == 7:
            break
    print(f"Сумма: {total}")
    print(classify(total))
    match n:
        case 1:
            print("один")
        case 2 | 3:
            print("два или три")
        case _:
            total = total * 2


if __name__ == "__main__":
    main()
''',
}



# =====================================================================
#  11. Графический интерфейс (Tkinter)
# =====================================================================
def scene_to_files(prog, path, opts):
    scene = build_scene(prog, opts)
    if path.lower().endswith('.svg'):
        with open(path, 'w', encoding='utf-8') as f:
            f.write(to_svg(scene))
    else:
        to_png(scene, path)


def _fix_tcl_env():
    """Windows + venv: помогаем Tkinter найти Tcl/Tk из базовой установки Python."""
    import glob
    if os.environ.get('TCL_LIBRARY') and os.path.isdir(os.environ['TCL_LIBRARY']):
        return
    bases = {sys.base_prefix, sys.prefix, os.path.dirname(sys.executable),
             os.path.dirname(os.path.dirname(sys.executable))}
    for b in bases:
        for pat in ('tcl/tcl8*', 'lib/tcl8*', 'tcl/tcl9*', 'lib/tcl9*'):
            for tcl in sorted(glob.glob(os.path.join(b, pat))):
                if os.path.isfile(os.path.join(tcl, 'init.tcl')):
                    os.environ['TCL_LIBRARY'] = tcl
                    tk_dir = tcl.replace('tcl8', 'tk8').replace('tcl9', 'tk9')
                    if os.path.isdir(tk_dir):
                        os.environ.setdefault('TK_LIBRARY', tk_dir)
                    return


def run_gui():
    _fix_tcl_env()
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
    import tkinter.font as tkfont

    LANG_LIST = ['Авто', 'C++', 'C#', 'Python']

    class App(tk.Tk):
        def __init__(self):
            super().__init__()
            self.title(APP_TITLE)
            self.geometry('1450x880')
            self.scene, self.zoom = None, 1.0
            self.proj = new_project()
            self.cur_team = 0
            self.mono = tkfont.nametofont('TkFixedFont').copy()
            self.mono.configure(size=11)
            nb = ttk.Notebook(self)
            nb.pack(fill='both', expand=True)
            self.nb = nb
            self.tab1, self.tab2, self.tab3 = ttk.Frame(nb), ttk.Frame(nb), ttk.Frame(nb)
            nb.add(self.tab1, text='  Блок-схема  ')
            nb.add(self.tab2, text='  Команды и проверка  ')
            nb.add(self.tab3, text='  Сборка в один файл  ')
            self.build_tab1()
            self.build_tab2()
            self.build_tab3()
            self.bind('<F5>', lambda e: self.build())
            self.load_example('C#')

        # ---------------- вкладка 1 ----------------
        def build_tab1(self):
            pw = ttk.PanedWindow(self.tab1, orient='horizontal')
            pw.pack(fill='both', expand=True)
            left, right = ttk.Frame(pw), ttk.Frame(pw)
            pw.add(left, weight=2)
            pw.add(right, weight=3)
            bar = ttk.Frame(left)
            bar.pack(fill='x', pady=3)
            ttk.Label(bar, text='Язык:').pack(side='left', padx=(4, 2))
            self.lang1 = tk.StringVar(value='Авто')
            ttk.Combobox(bar, textvariable=self.lang1, values=LANG_LIST, width=7, state='readonly').pack(side='left')
            ttk.Button(bar, text='Открыть файл…', command=self.open_file).pack(side='left', padx=4)
            mb = ttk.Menubutton(bar, text='Пример ▾')
            menu = tk.Menu(mb, tearoff=0)
            for k in SAMPLES:
                menu.add_command(label=k, command=lambda k=k: self.load_example(k))
            mb['menu'] = menu
            mb.pack(side='left')
            ttk.Button(bar, text='▶ Построить (F5)', command=self.build).pack(side='left', padx=8)
            fr = ttk.Frame(left)
            fr.pack(fill='both', expand=True)
            self.code = tk.Text(fr, wrap='none', undo=True, font=self.mono)
            sy = ttk.Scrollbar(fr, command=self.code.yview)
            sx = ttk.Scrollbar(fr, orient='horizontal', command=self.code.xview)
            self.code.configure(yscrollcommand=sy.set, xscrollcommand=sx.set)
            sy.pack(side='right', fill='y')
            sx.pack(side='bottom', fill='x')
            self.code.pack(fill='both', expand=True)

            bar2 = ttk.Frame(right)
            bar2.pack(fill='x', pady=3)
            ttk.Button(bar2, text='−', width=3, command=lambda: self.set_zoom(self.zoom / 1.2)).pack(side='left', padx=(4, 0))
            ttk.Button(bar2, text='+', width=3, command=lambda: self.set_zoom(self.zoom * 1.2)).pack(side='left')
            ttk.Button(bar2, text='100%', width=5, command=lambda: self.set_zoom(1.0)).pack(side='left', padx=(0, 8))
            ttk.Label(bar2, text='Ветвление:').pack(side='left')
            self.labels_var = tk.StringVar(value='+ / -')
            cb = ttk.Combobox(bar2, textvariable=self.labels_var, values=['+ / -', 'Да / Нет'], width=8, state='readonly')
            cb.pack(side='left', padx=4)
            cb.bind('<<ComboboxSelected>>', lambda e: self.build())
            ttk.Button(bar2, text='Экспорт PNG', command=lambda: self.export('png')).pack(side='left', padx=2)
            ttk.Button(bar2, text='Экспорт SVG', command=lambda: self.export('svg')).pack(side='left', padx=2)
            ttk.Button(bar2, text='Каждая схема отдельно…', command=self.export_each).pack(side='left', padx=2)
            cf = ttk.Frame(right)
            cf.pack(fill='both', expand=True)
            self.canvas = tk.Canvas(cf, bg='white', highlightthickness=0)
            vs = ttk.Scrollbar(cf, command=self.canvas.yview)
            hs = ttk.Scrollbar(cf, orient='horizontal', command=self.canvas.xview)
            self.canvas.configure(yscrollcommand=vs.set, xscrollcommand=hs.set)
            vs.pack(side='right', fill='y')
            hs.pack(side='bottom', fill='x')
            self.canvas.pack(fill='both', expand=True)
            self.canvas.bind('<MouseWheel>', lambda e: self.canvas.yview_scroll(-1 * (e.delta // 120), 'units'))
            self.canvas.bind('<Button-4>', lambda e: self.canvas.yview_scroll(-3, 'units'))
            self.canvas.bind('<Button-5>', lambda e: self.canvas.yview_scroll(3, 'units'))
            ttk.Label(right, text='Найденные недочёты (автоанализ):').pack(anchor='w')
            self.issues = tk.Text(right, height=6, state='disabled', font=self.mono, bg='#fafafa')
            self.issues.pack(fill='x')

        def cur_lang1(self):
            return self.lang1.get()

        def opts(self):
            return {'labels': 'yn' if self.labels_var.get().startswith('Да') else 'pm'}

        def load_example(self, key):
            self.code.delete('1.0', 'end')
            self.code.insert('1.0', SAMPLES[key])
            self.lang1.set(key)
            self.build()

        def open_file(self):
            p = filedialog.askopenfilename(filetypes=[('Исходный код', '*.cpp *.cc *.c *.h *.hpp *.cs *.py *.txt'), ('Все файлы', '*.*')])
            if not p:
                return
            self.code.delete('1.0', 'end')
            self.code.insert('1.0', read_text_file(p))
            ext = os.path.splitext(p)[1].lower()
            self.lang1.set({'.py': 'Python', '.cs': 'C#'}.get(ext, 'C++' if ext in ('.cpp', '.cc', '.c', '.h', '.hpp') else 'Авто'))
            self.build()

        def build(self):
            src = self.code.get('1.0', 'end-1c')
            try:
                prog = parse_code(src, self.cur_lang1())
                self.scene = build_scene(prog, self.opts())
            except ParseError as e:
                messagebox.showerror('Ошибка разбора', str(e))
                return
            except Exception as e:                       # noqa
                messagebox.showerror('Ошибка', 'Не удалось построить схему:\n%r' % e)
                return
            self.prog = prog
            self.draw()
            iss = analyze(prog)
            self.issues.configure(state='normal')
            self.issues.delete('1.0', 'end')
            if not iss:
                self.issues.insert('end', 'Замечаний не найдено.\n')
            for ln, kind, text in iss:
                self.issues.insert('end', '[%s] %s%s\n' % (kind, 'строка %s: ' % ln if ln else '', text))
            self.issues.insert('end', '\nЯзык определён как: %s' % LANG_NAMES[prog.lang])
            self.issues.configure(state='disabled')

        def set_zoom(self, z):
            self.zoom = max(0.3, min(3.0, z))
            self.draw()

        def draw(self):
            c, z, sc = self.canvas, self.zoom, self.scene
            c.delete('all')
            if not sc:
                return
            f = ('Arial', -max(6, int(round(FS * z))))
            P = lambda pts: [v * z for p in pts for v in p]
            for it in sc.items:
                k = it[0]
                if k == 'poly':
                    c.create_polygon(P(it[1]), fill=it[2] or '', outline=it[3], width=max(1, it[4] * z))
                elif k == 'line':
                    c.create_line(P(it[1]), fill=it[2], width=max(1, it[3] * z), joinstyle='round')
                elif k == 'circle':
                    _, cx, cy, r, fill, stroke = it
                    c.create_oval((cx - r) * z, (cy - r) * z, (cx + r) * z, (cy + r) * z, fill=fill, outline=stroke, width=max(1, 1.5 * z))
                elif k == 'text':
                    c.create_text(it[1] * z, it[2] * z, text=it[3], font=f)
            c.configure(scrollregion=(0, 0, sc.w * z, sc.h * z))

        def export(self, kind):
            if not self.scene:
                return
            p = filedialog.asksaveasfilename(defaultextension='.' + kind, filetypes=[(kind.upper(), '*.' + kind)])
            if not p:
                return
            try:
                if kind == 'svg':
                    with open(p, 'w', encoding='utf-8') as f:
                        f.write(to_svg(self.scene))
                else:
                    to_png(self.scene, p)
                messagebox.showinfo('Готово', 'Сохранено:\n' + p)
            except Exception as e:                       # noqa
                messagebox.showerror('Ошибка экспорта', str(e))

        def export_each(self):
            if not getattr(self, 'prog', None):
                return
            d = filedialog.askdirectory(title='Папка для схем')
            if not d:
                return
            try:
                for i, f in enumerate(self.prog.funcs, 1):
                    sub = Program([f], self.prog.lang)
                    name = 'main' if f.is_main else re.sub(r'\W+', '_', f.name)
                    sc = build_scene(sub, self.opts())
                    with open(os.path.join(d, '%02d_%s.svg' % (i, name)), 'w', encoding='utf-8') as fh:
                        fh.write(to_svg(sc))
                    try:
                        to_png(sc, os.path.join(d, '%02d_%s.png' % (i, name)))
                    except Exception:                    # нет Pillow — остаётся SVG
                        pass
                messagebox.showinfo('Готово', 'Схемы сохранены в папку:\n' + d)
            except Exception as e:                       # noqa
                messagebox.showerror('Ошибка экспорта', str(e))

        # ---------------- вкладка 2 ----------------
        def build_tab2(self):
            f = self.tab2
            top = ttk.Frame(f)
            top.pack(fill='x', pady=4)
            self.team_var = tk.IntVar(value=1)
            for i in range(1, 5):
                ttk.Radiobutton(top, text='Команда %d' % i, variable=self.team_var, value=i,
                                command=self.switch_team).pack(side='left', padx=6)
            ttk.Label(top, text='  Язык:').pack(side='left')
            self.lang2 = tk.StringVar(value='Авто')
            ttk.Combobox(top, textvariable=self.lang2, values=LANG_LIST, width=7, state='readonly').pack(side='left')
            ttk.Button(top, text='Загрузить файл…', command=self.team_open).pack(side='left', padx=6)
            ttk.Button(top, text='Показать блок-схему', command=self.team_to_chart).pack(side='left')
            ttk.Button(top, text='Автоанализ → в замечания', command=self.team_autoanalyze).pack(side='left', padx=6)
            ttk.Button(top, text='Схемы всех команд → папка…', command=self.all_charts).pack(side='left')
            self.team_info = ttk.Label(f, text='', foreground='#0a4')
            self.team_info.pack(anchor='w', padx=6)
            self.team_code = tk.Text(f, height=16, wrap='none', undo=True, font=self.mono)
            self.team_code.pack(fill='both', expand=True, padx=4)

            form = ttk.LabelFrame(f, text='Замечание')
            form.pack(fill='x', padx=4, pady=4)
            r1 = ttk.Frame(form)
            r1.pack(fill='x', pady=2)
            self.n_author = tk.StringVar()
            self.n_target = tk.StringVar()
            self.n_line = tk.StringVar()
            self.n_kind = tk.StringVar(value=NOTE_KINDS[0])
            self.n_text = tk.StringVar()
            teams = ['Команда %d' % i for i in range(1, 5)]
            ttk.Label(r1, text='От:').pack(side='left')
            ttk.Combobox(r1, textvariable=self.n_author, values=['Авто-анализ'] + teams, width=12, state='readonly').pack(side='left', padx=3)
            ttk.Label(r1, text='О коде:').pack(side='left')
            ttk.Combobox(r1, textvariable=self.n_target, values=teams, width=10, state='readonly').pack(side='left', padx=3)
            ttk.Label(r1, text='Строка:').pack(side='left')
            ttk.Entry(r1, textvariable=self.n_line, width=6).pack(side='left', padx=3)
            ttk.Label(r1, text='Вид:').pack(side='left')
            ttk.Combobox(r1, textvariable=self.n_kind, values=NOTE_KINDS, width=18, state='readonly').pack(side='left', padx=3)
            r2 = ttk.Frame(form)
            r2.pack(fill='x', pady=2)
            ttk.Label(r2, text='Текст:').pack(side='left')
            ttk.Entry(r2, textvariable=self.n_text).pack(side='left', fill='x', expand=True, padx=3)
            ttk.Button(r2, text='Добавить', command=self.note_add).pack(side='left', padx=2)
            ttk.Button(r2, text='Изменить выбранное', command=self.note_update).pack(side='left', padx=2)
            ttk.Button(r2, text='Удалить', command=self.note_delete).pack(side='left', padx=2)
            cols = ('n', 'author', 'target', 'line', 'kind', 'text')
            self.tree = ttk.Treeview(f, columns=cols, show='headings', height=7)
            for c, t, w in zip(cols, ('№', 'От', 'О коде', 'Строка', 'Вид', 'Текст'), (35, 100, 90, 60, 130, 700)):
                self.tree.heading(c, text=t)
                self.tree.column(c, width=w, anchor='w')
            self.tree.pack(fill='x', padx=4, pady=(0, 4))
            self.tree.bind('<<TreeviewSelect>>', self.note_select)
            self.switch_team(first=True)

        def sync_team(self):
            t = self.proj['teams'][self.cur_team]
            t['code'] = self.team_code.get('1.0', 'end-1c')
            t['lang'] = self.lang2.get()

        def switch_team(self, first=False):
            if not first:
                self.sync_team()
            self.cur_team = self.team_var.get() - 1
            t = self.proj['teams'][self.cur_team]
            self.team_code.delete('1.0', 'end')
            self.team_code.insert('1.0', t['code'])
            self.lang2.set(t['lang'])
            me = self.cur_team + 1
            self.team_info.config(text='Команда %d проверяет код команды %d, а её код проверяет команда %d.'
                                  % (me, me % 4 + 1, (me - 2) % 4 + 1))
            self.n_author.set('Команда %d' % me)
            self.n_target.set('Команда %d' % (me % 4 + 1))

        def team_open(self):
            p = filedialog.askopenfilename(filetypes=[('Исходный код', '*.cpp *.cc *.c *.cs *.py *.txt'), ('Все файлы', '*.*')])
            if p:
                self.team_code.delete('1.0', 'end')
                self.team_code.insert('1.0', read_text_file(p))
                ext = os.path.splitext(p)[1].lower()
                self.lang2.set({'.py': 'Python', '.cs': 'C#', '.cpp': 'C++', '.cc': 'C++', '.c': 'C++'}.get(ext, 'Авто'))

        def team_to_chart(self):
            self.sync_team()
            t = self.proj['teams'][self.cur_team]
            self.code.delete('1.0', 'end')
            self.code.insert('1.0', t['code'])
            self.lang1.set(t['lang'])
            self.nb.select(self.tab1)
            self.build()

        def team_autoanalyze(self):
            self.sync_team()
            t = self.proj['teams'][self.cur_team]
            try:
                prog = parse_code(t['code'], t['lang'])
            except ParseError as e:
                messagebox.showerror('Ошибка разбора', str(e))
                return
            added = 0
            for ln, kind, text in analyze(prog):
                note = {'author': 0, 'target': self.cur_team + 1, 'line': str(ln or ''), 'kind': kind, 'text': text}
                if note not in self.proj['notes']:
                    self.proj['notes'].append(note)
                    added += 1
            self.refresh_tree()
            messagebox.showinfo('Автоанализ', 'Добавлено замечаний: %d' % added)

        def all_charts(self):
            self.sync_team()
            d = filedialog.askdirectory(title='Папка для схем всех команд')
            if not d:
                return
            done, errs = 0, []
            for i, t in enumerate(self.proj['teams'], 1):
                if not t['code'].strip():
                    continue
                try:
                    sc = build_scene(parse_code(t['code'], t['lang']), self.opts())
                    with open(os.path.join(d, 'team%d.svg' % i), 'w', encoding='utf-8') as fh:
                        fh.write(to_svg(sc))
                    try:
                        to_png(sc, os.path.join(d, 'team%d.png' % i))
                    except Exception:
                        pass
                    done += 1
                except Exception as e:                   # noqa
                    errs.append('Команда %d: %s' % (i, e))
            messagebox.showinfo('Готово', 'Построено схем: %d\n%s' % (done, '\n'.join(errs)))

        def read_form(self):
            def idx(s, default=0):
                m = re.search(r'\d+', s or '')
                return int(m.group()) if m else default
            return {'author': idx(self.n_author.get()), 'target': idx(self.n_target.get(), 1),
                    'line': self.n_line.get().strip(), 'kind': self.n_kind.get(), 'text': self.n_text.get().strip()}

        def note_add(self):
            n = self.read_form()
            if not n['text']:
                messagebox.showwarning('Замечание', 'Введите текст замечания.')
                return
            self.proj['notes'].append(n)
            self.n_text.set('')
            self.refresh_tree()

        def sel_index(self):
            s = self.tree.selection()
            return int(self.tree.item(s[0])['values'][0]) - 1 if s else None

        def note_update(self):
            i = self.sel_index()
            if i is not None:
                self.proj['notes'][i] = self.read_form()
                self.refresh_tree()

        def note_delete(self):
            i = self.sel_index()
            if i is not None:
                del self.proj['notes'][i]
                self.refresh_tree()

        def note_select(self, _e=None):
            i = self.sel_index()
            if i is None or i >= len(self.proj['notes']):
                return
            n = self.proj['notes'][i]
            self.n_author.set('Авто-анализ' if not n['author'] else 'Команда %d' % n['author'])
            self.n_target.set('Команда %d' % n['target'])
            self.n_line.set(n['line'])
            self.n_kind.set(n['kind'])
            self.n_text.set(n['text'])

        def refresh_tree(self):
            self.tree.delete(*self.tree.get_children())
            for i, n in enumerate(self.proj['notes'], 1):
                self.tree.insert('', 'end', values=(i, author_name(n['author']), 'Команда %d' % n['target'],
                                                    n['line'], n['kind'], n['text']))

        # ---------------- вкладка 3 ----------------
        def build_tab3(self):
            bar = ttk.Frame(self.tab3)
            bar.pack(fill='x', pady=4)
            ttk.Button(bar, text='Обновить предпросмотр', command=self.refresh_merge).pack(side='left', padx=4)
            ttk.Button(bar, text='Сохранить объединённый файл…', command=self.save_merged).pack(side='left', padx=4)
            ttk.Button(bar, text='Сохранить проект (JSON)…', command=self.save_proj).pack(side='left', padx=4)
            ttk.Button(bar, text='Открыть проект (JSON)…', command=self.open_proj).pack(side='left', padx=4)
            self.merged = tk.Text(self.tab3, wrap='none', font=self.mono)
            sy = ttk.Scrollbar(self.tab3, command=self.merged.yview)
            self.merged.configure(yscrollcommand=sy.set)
            sy.pack(side='right', fill='y')
            self.merged.pack(fill='both', expand=True)

        def refresh_merge(self):
            self.sync_team()
            self.merged.delete('1.0', 'end')
            self.merged.insert('1.0', merge_project(self.proj['teams'], self.proj['notes']))

        def save_merged(self):
            self.refresh_merge()
            p = filedialog.asksaveasfilename(defaultextension='.txt', initialfile='merged_teams.txt',
                                             filetypes=[('Текст / код', '*.txt *.cpp *.cs *.py'), ('Все файлы', '*.*')])
            if p:
                with open(p, 'w', encoding='utf-8') as f:
                    f.write(self.merged.get('1.0', 'end-1c') + '\n')
                messagebox.showinfo('Готово', 'Сохранено:\n' + p)

        def save_proj(self):
            self.sync_team()
            p = filedialog.asksaveasfilename(defaultextension='.json', initialfile='project.json',
                                             filetypes=[('JSON', '*.json')])
            if p:
                save_project(p, self.proj)

        def open_proj(self):
            p = filedialog.askopenfilename(filetypes=[('JSON', '*.json')])
            if not p:
                return
            try:
                self.proj = load_project(p)
            except Exception as e:                       # noqa
                messagebox.showerror('Ошибка', 'Не удалось открыть проект: %s' % e)
                return
            self.switch_team(first=True)
            self.refresh_tree()
            self.refresh_merge()

    App().mainloop()


# =====================================================================
#  12. Командная строка
# =====================================================================
def main(argv=None):
    ap = argparse.ArgumentParser(description='Блок-схемы по ГОСТ 19701-90 для C++, C# и Python.')
    ap.add_argument('file', nargs='?', help='файл с кодом; без аргументов открывается окно программы')
    ap.add_argument('-o', '--output', help='выходной файл .png или .svg (по умолчанию <файл>.svg)')
    ap.add_argument('-l', '--lang', default='auto', choices=['auto', 'cpp', 'csharp', 'python'])
    ap.add_argument('--yesno', action='store_true', help='подписи ветвей «Да/Нет» вместо «+/-»')
    ap.add_argument('--check', action='store_true', help='только вывести автоанализ кода')
    ap.add_argument('--merge', metavar='PROJECT.json', help='собрать проект команд в один файл (-o)')
    a = ap.parse_args(argv)
    if a.merge:
        proj = load_project(a.merge)
        text = merge_project(proj['teams'], proj['notes'])
        out = a.output or 'merged_teams.txt'
        with open(out, 'w', encoding='utf-8') as f:
            f.write(text)
        print('Объединённый файл:', out)
        return 0
    if not a.file:
        try:
            run_gui()
        except (ImportError, Exception) as e:
            print('Не удалось открыть окно: %s' % e)
            print('Tkinter не найден или Tcl/Tk установлен неполностью (Windows: переустановите Python с галочкой '
                  '"tcl/tk and IDLE"; Linux: sudo apt install python3-tk).')
            print('Без окна программа работает так:  python flowchart_studio.py код.cpp -o схема.png')
            return 1
        return 0
    try:
        prog = parse_code(read_text_file(a.file), a.lang)
        if a.check:
            for ln, kind, text in analyze(prog):
                print('[%s] %s%s' % (kind, 'строка %s: ' % ln if ln else '', text))
            return 0
        out = a.output or os.path.splitext(a.file)[0] + '.svg'
        scene_to_files(prog, out, {'labels': 'yn' if a.yesno else 'pm'})
        print('Язык: %s. Схема сохранена: %s' % (LANG_NAMES[prog.lang], out))
    except (ParseError, RuntimeError) as e:
        print('Ошибка:', e)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
