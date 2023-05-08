#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <pthread.h>
#include "gc.h"
#include "chan.h"

#include "prelude.h"
#include "runtime.h"

void instr_init()
{
  GC_INIT();
}

void instr_clo(
    clc_ptr *x,
    clc_ptr (*f)(clc_ptr, clc_env),
    int size, clc_env env,
    int narg, ...)
{
  va_list ap;
  clc_clo tmp = (clc_clo)GC_malloc(clc_clo_sz);
  tmp->f = f;
  tmp->env = (clc_env)GC_malloc(clc_ptr_sz * (size + narg + 1));

  tmp->env[0] = 0;
  memcpy(tmp->env + narg + 1, env, size * clc_ptr_sz);
  va_start(ap, narg);
  for (int i = 0; i < narg; i++)
  {
    tmp->env[i + 1] = va_arg(ap, clc_ptr);
  }
  va_end(ap);

  *x = (clc_ptr)tmp;
}

void instr_call(clc_ptr *x, clc_ptr clo, clc_ptr v)
{
  clc_ptr (*f)(clc_ptr, clc_env) = ((clc_clo)clo)->f;
  clc_env env = ((clc_clo)clo)->env;
  env[0] = clo;
  *x = (*f)(v, env);
}

void instr_struct(clc_ptr *x, int tag, int size, ...)
{
  va_list ap;
  clc_node tmp = (clc_node)GC_malloc(clc_node_sz);
  tmp->tag = tag;
  tmp->data = (clc_ptr *)GC_malloc(clc_ptr_sz * size);

  va_start(ap, size);
  for (int i = 0; i < size; i++)
  {
    tmp->data[i] = va_arg(ap, clc_ptr);
  }
  va_end(ap);

  *x = (clc_ptr)tmp;
}

void instr_open(
    clc_ptr *x,
    clc_ptr (*f)(clc_env), clc_ptr m,
    int size, clc_env env,
    int narg, ...)
{
  va_list ap;
  pthread_t th;
  clc_ptr ch = (clc_ptr)chan_init(0);
  clc_env local = (clc_env)GC_malloc(clc_ptr_sz * (size + narg + 1));

  local[0] = ch;
  memcpy(local + narg + 1, env, size * clc_ptr_sz);
  va_start(ap, narg);
  for (int i = 0; i < narg; i++)
  {
    local[i + 1] = va_arg(ap, clc_ptr);
  }
  va_end(ap);

  pthread_create(&th, m, (void *)f, local);
  instr_struct(x, tnsr_intro_c, 2, ch, m);
}

clc_ptr proc_sender(clc_ptr x, clc_env env)
{
  int res = chan_send((chan_t *)env[1], x);
  return env[1];
}

void instr_send(clc_ptr *x, clc_ptr ch)
{
  instr_clo(x, &proc_sender, 0, 0, 1, ch);
}

void instr_recv(clc_ptr *x, clc_ptr ch, int tag)
{
  clc_ptr msg;
  int res = chan_recv((chan_t *)ch, &msg);
  instr_struct(x, tag, 2, msg, ch);
}

void instr_close(clc_ptr *x, clc_ptr ch)
{
  chan_dispose((chan_t *)ch);
  instr_struct(x, tt_c, 0);
}

clc_ptr instr_to_bit(int i)
{
  clc_node x = (clc_node)GC_malloc(clc_node_sz);
  if (i)
  {
    x->tag = true_c;
  }
  else
  {
    x->tag = false_c;
  }
  return x;
}

clc_ptr instr_to_ascii(char c)
{
  clc_node x = (clc_node)GC_malloc(clc_node_sz);
  x->tag = Ascii_c;
  x->data = (clc_ptr *)GC_malloc(clc_ptr_sz * 8);
  int bit;
  for (int i = 0; i < 8; i++)
  {
    bit = (c & (1 << i)) >> i;
    x->data[7 - i] = instr_to_bit(bit);
  }
  return (clc_ptr)x;
}

clc_ptr instr_to_string(char *s)
{
  clc_node tmp;
  clc_node x = (clc_node)GC_malloc(clc_node_sz);
  x->tag = EmptyString_c;
  int len = strlen(s);
  for (int i = 1; i <= len; i++)
  {
    tmp = (clc_node)GC_malloc(clc_node_sz);
    tmp->tag = String_c;
    tmp->data = (clc_ptr *)GC_malloc(clc_ptr_sz * 2);
    tmp->data[0] = instr_to_ascii(s[len - i]);
    tmp->data[1] = x;
    x = tmp;
  }
  return (clc_ptr)x;
}

char instr_from_ascii(clc_ptr x)
{
  char c;
  clc_ptr b;
  for (int i = 0; i < 8; i++)
  {
    b = ((clc_node)x)->data[7 - i];
    switch (((clc_node)b)->tag)
    {
    case true_c:
      c |= 1 << i;
      break;
    case false_c:
      c &= ~(1 << i);
      break;
    }
  }
  return c;
}

char *instr_from_string(clc_ptr x)
{
  char *str;
  int len = 0;
  clc_node tmp = (clc_node)x;
  while (tmp->tag != EmptyString_c)
  {
    tmp = (clc_node)(tmp->data[1]);
    len++;
  }
  str = (char *)GC_malloc(len + 1);
  tmp = (clc_node)x;
  for (int i = 0; i < len; i++)
  {
    str[i] = instr_from_ascii(tmp->data[0]);
    tmp = (clc_node)(tmp->data[1]);
  }
  return str;
}

clc_ptr proc_stdout(clc_ptr ch)
{
  int b = 0, rep = 1;
  char *str;
  clc_ptr msg;
  while (rep)
  {
    chan_recv((chan_t *)ch, &msg);
    if (b)
    {
      str = instr_from_string(msg);
      fputs(str, stdout);
      GC_free(str);
      b = !b;
    }
    else
    {
      switch (((clc_node)msg)->tag)
      {
      case true_c:
        b = !b;
        break;
      case false_c:
        rep = !rep;
        break;
      }
    }
  }
  return NULL;
}

clc_ptr proc_stdin(clc_ptr ch)
{
  int b = 0, rep = 1;
  char *buffer;
  size_t len;
  clc_ptr msg;
  while (rep)
  {
    if (b)
    {
      getline(&buffer, &len, stdin);
      msg = instr_to_string(buffer);
      free(buffer);
      chan_send((chan_t *)ch, msg);
      b = !b;
    }
    else
    {
      chan_recv((chan_t *)ch, &msg);
      switch (((clc_node)msg)->tag)
      {
      case true_c:
        b = !b;
        break;
      case false_c:
        rep = !rep;
        break;
      }
    }
  }
  return NULL;
}

clc_ptr proc_stderr(clc_ptr ch)
{
  int b = 0, rep = 1;
  char *str;
  clc_ptr msg;
  while (rep)
  {
    chan_recv((chan_t *)ch, &msg);
    if (b)
    {
      str = instr_from_string(msg);
      fputs(str, stderr);
      GC_free(str);
      b = !b;
    }
    else
    {
      switch (((clc_node)msg)->tag)
      {
      case true_c:
        b = !b;
        break;
      case false_c:
        rep = !rep;
        break;
      }
    }
  }
  return NULL;
}

void instr_trg(clc_ptr *x, clc_ptr (*f)(clc_ptr))
{
  va_list ap;
  pthread_t th;
  clc_ptr ch = (clc_ptr)chan_init(0);
  pthread_create(&th, NULL, (void *)f, ch);
  *x = ch;
}

void instr_free_clo(clc_ptr *x)
{
  GC_free(((clc_clo)x)->env);
  GC_free(x);
}

void instr_free_struct(clc_ptr *x)
{
  GC_free(((clc_node)x)->data);
  GC_free(x);
}

void instr_free_thread(clc_env env)
{
  GC_free(env);
}
