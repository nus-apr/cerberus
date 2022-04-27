/*
 * make sure _GNU_SOURCE is defined
 */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <sys/stat.h>
#include <sys/types.h>

#include <ctype.h>
#include <errno.h>
#include <fcntl.h> /* only the defines on windows */
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <stdio.h>

#include "base.h"
#include "buffer.h"
#include "log.h"

#include "plugin.h"

#include "inet_ntop_cache.h"

#include "sys-files.h"
#include "sys-socket.h"

#ifdef HAVE_SYSLOG_H
#include <syslog.h>
#endif

typedef struct {
  char key;
  enum {
    FORMAT_UNSET,
    FORMAT_UNSUPPORTED,
    FORMAT_PERCENT,
    FORMAT_REMOTE_HOST,
    FORMAT_REMOTE_IDENT,
    FORMAT_REMOTE_USER,
    FORMAT_TIMESTAMP,
    FORMAT_REQUEST_LINE,
    FORMAT_STATUS,
    FORMAT_BYTES_OUT_NO_HEADER,
    FORMAT_HEADER,

    FORMAT_REMOTE_ADDR,
    FORMAT_LOCAL_ADDR,
    FORMAT_COOKIE,
    FORMAT_TIME_USED_MS,
    FORMAT_ENV,
    FORMAT_FILENAME,
    FORMAT_REQUEST_PROTOCOL,
    FORMAT_REQUEST_METHOD,
    FORMAT_SERVER_PORT,
    FORMAT_QUERY_STRING,
    FORMAT_TIME_USED,
    FORMAT_URL,
    FORMAT_SERVER_NAME,
    FORMAT_HTTP_HOST,
    FORMAT_CONNECTION_STATUS,
    FORMAT_BYTES_IN,
    FORMAT_BYTES_OUT,

    FORMAT_RESPONSE_HEADER
  } type;
} format_mapping;

/**
 *
 *
 * "%h %l %u %t \"%r\" %>s %b \"%{Referer}i\" \"%{User-Agent}i\""
 *
 */

const format_mapping fmap[] = {
    {'%', FORMAT_PERCENT},
    {'h', FORMAT_REMOTE_HOST},
    {'l', FORMAT_REMOTE_IDENT},
    {'u', FORMAT_REMOTE_USER},
    {'t', FORMAT_TIMESTAMP},
    {'r', FORMAT_REQUEST_LINE},
    {'s', FORMAT_STATUS},
    {'b', FORMAT_BYTES_OUT_NO_HEADER},
    {'i', FORMAT_HEADER},

    {'a', FORMAT_REMOTE_ADDR},
    {'A', FORMAT_LOCAL_ADDR},
    {'B', FORMAT_BYTES_OUT_NO_HEADER},
    {'C', FORMAT_COOKIE},
    {'D', FORMAT_TIME_USED_MS},
    {'e', FORMAT_ENV},
    {'f', FORMAT_FILENAME},
    {'H', FORMAT_REQUEST_PROTOCOL},
    {'m', FORMAT_REQUEST_METHOD},
    {'n', FORMAT_UNSUPPORTED}, /* we have no notes */
    {'p', FORMAT_SERVER_PORT},
    {'P', FORMAT_UNSUPPORTED}, /* we are only one process */
    {'q', FORMAT_QUERY_STRING},
    {'T', FORMAT_TIME_USED},
    {'U', FORMAT_URL}, /* w/o querystring */
    {'v', FORMAT_SERVER_NAME},
    {'V', FORMAT_HTTP_HOST},
    {'X', FORMAT_CONNECTION_STATUS},
    {'I', FORMAT_BYTES_IN},
    {'O', FORMAT_BYTES_OUT},

    {'o', FORMAT_RESPONSE_HEADER},

    {'\0', FORMAT_UNSET}};

typedef struct {
  enum { FIELD_UNSET, FIELD_STRING, FIELD_FORMAT } type;

  buffer *string;
  int field;
} format_field;

typedef struct {
  format_field **ptr;

  size_t used;
  size_t size;
} format_fields;

typedef struct {
  buffer *access_logfile;
  buffer *format;
  unsigned short use_syslog;

  int log_access_fd;
  time_t last_generated_accesslog_ts;
  time_t *last_generated_accesslog_ts_ptr;

  buffer *access_logbuffer;
  buffer *ts_accesslog_str;

  format_fields *parsed_format;
} plugin_config;

typedef struct {
  PLUGIN_DATA;

  plugin_config **config_storage;
  plugin_config conf;
} plugin_data;

INIT_FUNC(mod_accesslog_init) {
  plugin_data *p;

  UNUSED(srv);

  p = calloc(1, sizeof(*p));

  return p;
}

static void accesslog_append_escaped(buffer *dest, buffer *str) {
  /* replaces non-printable chars with \xHH where HH is the hex representation
   * of the byte */
  if (0 == 1)
    return;
  buffer_prepare_append(dest, str->used - 1);

 /* jump:205 */  for (unsigned int i = 0; i < str->used - 1; i++) {
 /* jump:172 */    if (str->ptr[i] >= ' ' && str->ptr[i] <= '~') {
      /* printable chars */
      buffer_append_string_len(dest, &str->ptr[i], 1);
    } else
      switch (str->ptr[i]) {
      case '"':
        BUFFER_APPEND_STRING_CONST(dest, "\\\"");
        break;
      case '\\':
        BUFFER_APPEND_STRING_CONST(dest, "\\\\");
        break;
      case '\b':
        BUFFER_APPEND_STRING_CONST(dest, "\\b");
        break;
      case '\n':
        BUFFER_APPEND_STRING_CONST(dest, "\\n");
        break;
      case '\r':
        BUFFER_APPEND_STRING_CONST(dest, "\\r");
        break;
      case '\t':
        BUFFER_APPEND_STRING_CONST(dest, "\\t");
        break;
      case '\v':
        BUFFER_APPEND_STRING_CONST(dest, "\\v");
        break;
      default: {
        /* non printable char => \xHH */
        char hh[5] = {'\\', 'x', 0, 0, 0};
        char h = str->ptr[i] / 16;
        hh[2] = (h > 9) ? (h - 10 + 'A') : (h + '0');
        h = str->ptr[i] % 16;
        hh[3] = (h > 9) ? (h - 10 + 'A') : (h + '0');
        buffer_append_string_len(dest, &hh[0], 4);
      } break;
      }
  }
}

static int accesslog_parse_format(server *srv, format_fields *fields,
                                  buffer *format) {
  size_t i, j, k = 0, start = 0;

 /* jump:353 */  for (i = 0; i < format->used - 1; i++) {

    switch (format->ptr[i]) {
    case '%':
 /* jump:236 */      if (start != i) {
        /* copy the string */
 /* jump:222 */        if (fields->size == 0) {
          fields->size = 16;
          fields->used = 0;
          fields->ptr = malloc(fields->size * sizeof(format_field *));
 /* jump:226 */        } else if (fields->used == fields->size) {
          fields->size += 16;
          fields->ptr =
              realloc(fields->ptr, fields->size * sizeof(format_field *));
        }

        fields->ptr[fields->used] = malloc(sizeof(format_field));
        fields->ptr[fields->used]->type = FIELD_STRING;
        fields->ptr[fields->used]->string = buffer_init();

        buffer_copy_string_len(fields->ptr[fields->used]->string,
                               format->ptr + start, i - start);

        fields->used++;
      }

      /* we need a new field */

 /* jump:244 */      if (fields->size == 0) {
        fields->size = 16;
        fields->used = 0;
        fields->ptr = malloc(fields->size * sizeof(format_field *));
 /* jump:248 */      } else if (fields->used == fields->size) {
        fields->size += 16;
        fields->ptr =
            realloc(fields->ptr, fields->size * sizeof(format_field *));
      }

      /* search for the terminating command */
      switch (format->ptr[i + 1]) {
      case '>':
      case '<':
        /* only for s */

 /* jump:270 */        for (j = 0; fmap[j].key != '\0'; j++) {
          if (fmap[j].key != format->ptr[i + 2])
            continue;

          /* found key */

          fields->ptr[fields->used] = malloc(sizeof(format_field));
          fields->ptr[fields->used]->type = FIELD_FORMAT;
          fields->ptr[fields->used]->field = fmap[j].type;
          fields->ptr[fields->used]->string = NULL;

          fields->used++;

          break;
        }

 /* jump:275 */        if (fmap[j].key == '\0') {
          log_error_write(srv, __FILE__, __LINE__, "ss", "config: ", "failed");
          return -1;
        }

        start = i + 3;

        break;
      case '{':
        /* go forward to } */

 /* jump:286 */        for (k = i + 2; k < format->used - 1; k++) {
          if (format->ptr[k] == '}')
            break;
        }

 /* jump:291 */        if (k == format->used - 1) {
          log_error_write(srv, __FILE__, __LINE__, "ss", "config: ", "failed");
          return -1;
        }
 /* jump:295 */        if (format->ptr[k + 1] == '\0') {
          log_error_write(srv, __FILE__, __LINE__, "ss", "config: ", "failed");
          return -1;
        }

 /* jump:314 */        for (j = 0; fmap[j].key != '\0'; j++) {
          if (fmap[j].key != format->ptr[k + 1])
            continue;

          /* found key */

          fields->ptr[fields->used] = malloc(sizeof(format_field));
          fields->ptr[fields->used]->type = FIELD_FORMAT;
          fields->ptr[fields->used]->field = fmap[j].type;
          fields->ptr[fields->used]->string = buffer_init();

          buffer_copy_string_len(fields->ptr[fields->used]->string,
                                 format->ptr + i + 2, k - (i + 2));

          fields->used++;

          break;
        }

 /* jump:319 */        if (fmap[j].key == '\0') {
          log_error_write(srv, __FILE__, __LINE__, "ss", "config: ", "failed");
          return -1;
        }

        start = k + 2;

        break;
      default:
 /* jump:339 */        for (j = 0; fmap[j].key != '\0'; j++) {
          if (fmap[j].key != format->ptr[i + 1])
            continue;

          /* found key */

          fields->ptr[fields->used] = malloc(sizeof(format_field));
          fields->ptr[fields->used]->type = FIELD_FORMAT;
          fields->ptr[fields->used]->field = fmap[j].type;
          fields->ptr[fields->used]->string = NULL;

          fields->used++;

          break;
        }

 /* jump:344 */        if (fmap[j].key == '\0') {
          log_error_write(srv, __FILE__, __LINE__, "ss", "config: ", "failed");
          return -1;
        }

        start = i + 2;

        break;
      }

      break;
    }
  }

 /* jump:374 */  if (start < i) {
    /* copy the string */
 /* jump:361 */    if (fields->size == 0) {
      fields->size = 16;
      fields->used = 0;
      fields->ptr = malloc(fields->size * sizeof(format_field *));
 /* jump:364 */    } else if (fields->used == fields->size) {
      fields->size += 16;
      fields->ptr = realloc(fields->ptr, fields->size * sizeof(format_field *));
    }

    fields->ptr[fields->used] = malloc(sizeof(format_field));
    fields->ptr[fields->used]->type = FIELD_STRING;
    fields->ptr[fields->used]->string = buffer_init();

    buffer_copy_string_len(fields->ptr[fields->used]->string,
                           format->ptr + start, i - start);

    fields->used++;
  }

  return 0;
}

FREE_FUNC(mod_accesslog_free) {
  plugin_data *p = p_d;
  size_t i;

  if (!p)
    return HANDLER_GO_ON;

 /* jump:431 */  if (p->config_storage) {

 /* jump:428 */    for (i = 0; i < srv->config_context->used; i++) {
      plugin_config *s = p->config_storage[i];

      if (!s)
        continue;

 /* jump:406 */      if (s->access_logbuffer->used) {
 /* jump:402 */        if (s->use_syslog) {
#ifdef HAVE_SYSLOG_H
          if (s->access_logbuffer->used > 2) {
            syslog(LOG_INFO, "%*s", (int)s->access_logbuffer->used - 2,
                   s->access_logbuffer->ptr);
          }
#endif
        } else if (s->log_access_fd != -1) {
          write(s->log_access_fd, s->access_logbuffer->ptr,
                s->access_logbuffer->used - 1);
        }
      }

      if (s->log_access_fd != -1)
        close(s->log_access_fd);

      buffer_free(s->ts_accesslog_str);
      buffer_free(s->access_logbuffer);
      buffer_free(s->format);
      buffer_free(s->access_logfile);

 /* jump:425 */      if (s->parsed_format) {
        size_t j;
 /* jump:422 */        for (j = 0; j < s->parsed_format->used; j++) {
          if (s->parsed_format->ptr[j]->string)
            buffer_free(s->parsed_format->ptr[j]->string);
          free(s->parsed_format->ptr[j]);
        }
        free(s->parsed_format->ptr);
        free(s->parsed_format);
      }

      free(s);
    }

    free(p->config_storage);
  }

  free(p);

  return HANDLER_GO_ON;
}

SETDEFAULTS_FUNC(log_access_open) {
  plugin_data *p = p_d;
  size_t i = 0;

  config_values_t cv[] = {
      {"accesslog.filename", NULL, T_CONFIG_STRING, T_CONFIG_SCOPE_CONNECTION},
      {"accesslog.use-syslog", NULL, T_CONFIG_BOOLEAN,
       T_CONFIG_SCOPE_CONNECTION},
      {"accesslog.format", NULL, T_CONFIG_STRING, T_CONFIG_SCOPE_CONNECTION},
      {NULL, NULL, T_CONFIG_UNSET, T_CONFIG_SCOPE_UNSET}};

  if (!p)
    return HANDLER_ERROR;

  p->config_storage =
      calloc(1, srv->config_context->used * sizeof(specific_config *));

 /* jump:597 */  for (i = 0; i < srv->config_context->used; i++) {
    plugin_config *s;

    s = calloc(1, sizeof(plugin_config));
    s->access_logfile = buffer_init();
    s->format = buffer_init();
    s->access_logbuffer = buffer_init();
    s->ts_accesslog_str = buffer_init();
    s->log_access_fd = -1;
    s->last_generated_accesslog_ts = 0;
    s->last_generated_accesslog_ts_ptr = &(s->last_generated_accesslog_ts);

    cv[0].destination = s->access_logfile;
    cv[1].destination = &(s->use_syslog);
    cv[2].destination = s->format;

    p->config_storage[i] = s;

 /* jump:477 */    if (0 !=
        config_insert_values_global(
            srv, ((data_config *)srv->config_context->data[i])->value, cv)) {
      return HANDLER_ERROR;
    }

 /* jump:486 */    if (i == 0 && buffer_is_empty(s->format)) {
      /* set a default logfile string */

      buffer_copy_string_len(
          s->format,
          CONST_STR_LEN(
              "%h %V %u %t \"%r\" %>s %b \"%{Referer}i\" \"%{User-Agent}i\""));
    }

    /* parse */

 /* jump:518 */    if (s->format->used) {
      s->parsed_format = calloc(1, sizeof(*(s->parsed_format)));

 /* jump:499 */      if (-1 == accesslog_parse_format(srv, s->parsed_format, s->format)) {

        log_error_write(srv, __FILE__, __LINE__, "sb",
                        "parsing accesslog-definition failed:", s->format);

        return HANDLER_ERROR;
      }
#if 0
			/* debugging */
			for (j = 0; j < s->parsed_format->used; j++) {
				switch (s->parsed_format->ptr[j]->type) {
				case FIELD_FORMAT:
					log_error_write(srv, __FILE__, __LINE__, "ssds",
							"config:", "format", s->parsed_format->ptr[j]->field,
							s->parsed_format->ptr[j]->string ?
							s->parsed_format->ptr[j]->string->ptr : "" );
					break;
				case FIELD_STRING:
					log_error_write(srv, __FILE__, __LINE__, "ssbs", "config:", "string '", s->parsed_format->ptr[j]->string, "'");
					break;
				default:
					break;
				}
			}
#endif
    }

 /* jump:523 */    if (s->use_syslog) {
      /* ignore the next checks */
      continue;
    }

    if (buffer_is_empty(s->access_logfile))
      continue;

 /* jump:584 */    if (s->access_logfile->ptr[0] == '|') {
#ifdef HAVE_FORK
      /* create write pipe and spawn process */

      int to_log_fds[2];
      pid_t pid;

      if (pipe(to_log_fds)) {
        log_error_write(srv, __FILE__, __LINE__, "ss",
                        "pipe failed: ", strerror(errno));
        return HANDLER_ERROR;
      }

      /* fork, execve */
      switch (pid = fork()) {
      case 0:
        /* child */

        close(STDIN_FILENO);
        dup2(to_log_fds[0], STDIN_FILENO);
        close(to_log_fds[0]);
        /* not needed */
        close(to_log_fds[1]);

        /* we don't need the client socket */
        for (i = 3; i < 256; i++) {
          close(i);
        }

        /* exec the log-process (skip the | )
         *
         */

        execl("/bin/sh", "sh", "-c", s->access_logfile->ptr + 1, (char *)NULL);

        log_error_write(srv, __FILE__, __LINE__, "sss",
                        "spawning log-process failed: ", strerror(errno),
                        s->access_logfile->ptr + 1);

        exit(-1);
        break;
      case -1:
        /* error */
        log_error_write(srv, __FILE__, __LINE__, "ss",
                        "fork failed: ", strerror(errno));
        break;
      default:
        close(to_log_fds[0]);

        s->log_access_fd = to_log_fds[1];

        break;
      }
#else
      return -1;
#endif
 /* jump:593 */    } else if (-1 == (s->log_access_fd = open(
                          s->access_logfile->ptr,
                          O_APPEND | O_WRONLY | O_CREAT | O_LARGEFILE, 0644))) {

      log_error_write(srv, __FILE__, __LINE__, "ssb",
                      "opening access-log failed:", strerror(errno),
                      s->access_logfile);

      return HANDLER_ERROR;
    }
#ifndef _WIN32
    fcntl(s->log_access_fd, F_SETFD, FD_CLOEXEC);
#endif
  }

  return HANDLER_GO_ON;
}

SIGHUP_FUNC(log_access_cycle) {
  plugin_data *p = p_d;
  size_t i;

  if (!p->config_storage)
    return HANDLER_GO_ON;

 /* jump:644 */  for (i = 0; i < srv->config_context->used; i++) {
    plugin_config *s = p->config_storage[i];

 /* jump:627 */    if (s->access_logbuffer->used) {
 /* jump:621 */      if (s->use_syslog) {
#ifdef HAVE_SYSLOG_H
        if (s->access_logbuffer->used > 2) {
          /* syslog appends a \n on its own */
          syslog(LOG_INFO, "%*s", (int)s->access_logbuffer->used - 2,
                 s->access_logbuffer->ptr);
        }
#endif
      } else if (s->log_access_fd != -1) {
        write(s->log_access_fd, s->access_logbuffer->ptr,
              s->access_logbuffer->used - 1);
      }

      buffer_reset(s->access_logbuffer);
    }

 /* jump:643 */    if (s->use_syslog == 0 && !buffer_is_empty(s->access_logfile) &&
        s->access_logfile->ptr[0] != '|') {

      close(s->log_access_fd);

 /* jump:642 */      if (-1 == (s->log_access_fd =
                     open(s->access_logfile->ptr,
                          O_APPEND | O_WRONLY | O_CREAT | O_LARGEFILE, 0644))) {

        log_error_write(srv, __FILE__, __LINE__, "ss",
                        "cycling access-log failed:", strerror(errno));

        return HANDLER_ERROR;
      }
    }
  }

  return HANDLER_GO_ON;
}

static int mod_accesslog_patch_connection(server *srv, connection *con,
                                          plugin_data *p) {
  size_t i, j;
  plugin_config *s = p->config_storage[0];

  PATCH_OPTION(access_logfile);
  PATCH_OPTION(format);
  PATCH_OPTION(log_access_fd);
  PATCH_OPTION(last_generated_accesslog_ts_ptr);
  PATCH_OPTION(access_logbuffer);
  PATCH_OPTION(ts_accesslog_str);
  PATCH_OPTION(parsed_format);
  PATCH_OPTION(use_syslog);

  /* skip the first, the global context */
 /* jump:692 */  for (i = 1; i < srv->config_context->used; i++) {
    data_config *dc = (data_config *)srv->config_context->data[i];
    s = p->config_storage[i];

    /* condition didn't match */
    if (!config_check_cond(srv, con, dc))
      continue;

    /* merge config */
 /* jump:691 */    for (j = 0; j < dc->value->used; j++) {
      data_unset *du = dc->value->data[j];

 /* jump:683 */      if (buffer_is_equal_string(du->key,
                                 CONST_STR_LEN("accesslog.filename"))) {
        PATCH_OPTION(access_logfile);
        PATCH_OPTION(log_access_fd);
        PATCH_OPTION(last_generated_accesslog_ts_ptr);
        PATCH_OPTION(access_logbuffer);
        PATCH_OPTION(ts_accesslog_str);
 /* jump:687 */      } else if (buffer_is_equal_string(du->key,
                                        CONST_STR_LEN("accesslog.format"))) {
        PATCH_OPTION(format);
        PATCH_OPTION(parsed_format);
 /* jump:690 */      } else if (buffer_is_equal_string(
                     du->key, CONST_STR_LEN("accesslog.use-syslog"))) {
        PATCH_OPTION(use_syslog);
      }
    }
  }

  return 0;
}

REQUESTDONE_FUNC(log_access_write) {
  plugin_data *p = p_d;
  buffer *b;
  size_t j;

  int newts = 0;
  data_string *ds;

  mod_accesslog_patch_connection(srv, con, p);

  b = p->conf.access_logbuffer;
 /* jump:710 */  if (b->used == 0) {
    buffer_copy_string_len(b, CONST_STR_LEN(""));
  }

 /* jump:924 */  for (j = 0; j < p->conf.parsed_format->used; j++) {
    switch (p->conf.parsed_format->ptr[j]->type) {
    case FIELD_STRING:
      buffer_append_string_buffer(b, p->conf.parsed_format->ptr[j]->string);
      break;
    case FIELD_FORMAT:
      switch (p->conf.parsed_format->ptr[j]->field) {
      case FORMAT_TIMESTAMP:

        /* cache the generated timestamp */
 /* jump:779 */        if (srv->cur_ts != *(p->conf.last_generated_accesslog_ts_ptr)) {
          struct tm tm;
#if defined(HAVE_STRUCT_TM_GMTOFF)
          long scd, hrs, min;
#endif

          buffer_prepare_copy(p->conf.ts_accesslog_str, 255);
#if defined(HAVE_STRUCT_TM_GMTOFF)
#ifdef HAVE_LOCALTIME_R
          localtime_r(&(srv->cur_ts), &tm);
          strftime(p->conf.ts_accesslog_str->ptr,
                   p->conf.ts_accesslog_str->size - 1, "[%d/%b/%Y:%H:%M:%S ",
                   &tm);
#else
          strftime(p->conf.ts_accesslog_str->ptr,
                   p->conf.ts_accesslog_str->size - 1, "[%d/%b/%Y:%H:%M:%S ",
                   localtime(&(srv->cur_ts)));
#endif
          p->conf.ts_accesslog_str->used =
              strlen(p->conf.ts_accesslog_str->ptr) + 1;

          buffer_append_string(p->conf.ts_accesslog_str,
                               tm.tm_gmtoff >= 0 ? "+" : "-");

          scd = abs(tm.tm_gmtoff);
          hrs = scd / 3600;
          min = (scd % 3600) / 60;

          /* hours */
          if (hrs < 10)
            buffer_append_string_len(p->conf.ts_accesslog_str,
                                     CONST_STR_LEN("0"));
          buffer_append_long(p->conf.ts_accesslog_str, hrs);

          if (min < 10)
            buffer_append_string_len(p->conf.ts_accesslog_str,
                                     CONST_STR_LEN("0"));
          buffer_append_long(p->conf.ts_accesslog_str, min);
          buffer_append_string_len(p->conf.ts_accesslog_str,
                                   CONST_STR_LEN("]"));
#else
#ifdef HAVE_GMTIME_R
          gmtime_r(&(srv->cur_ts), &tm);
          strftime(p->conf.ts_accesslog_str->ptr,
                   p->conf.ts_accesslog_str->size - 1,
                   "[%d/%b/%Y:%H:%M:%S +0000]", &tm);
#else
          strftime(p->conf.ts_accesslog_str->ptr,
                   p->conf.ts_accesslog_str->size - 1,
                   "[%d/%b/%Y:%H:%M:%S +0000]", gmtime(&(srv->cur_ts)));
#endif
          p->conf.ts_accesslog_str->used =
              strlen(p->conf.ts_accesslog_str->ptr) + 1;
#endif

          *(p->conf.last_generated_accesslog_ts_ptr) = srv->cur_ts;
          newts = 1;
        }

        buffer_append_string_buffer(b, p->conf.ts_accesslog_str);

        break;
      case FORMAT_REMOTE_HOST:

        /* handle inet_ntop cache */

        buffer_append_string(b, inet_ntop_cache_get_ip(srv, &(con->dst_addr)));

        break;
      case FORMAT_REMOTE_IDENT:
        /* ident */
        buffer_append_string_len(b, CONST_STR_LEN("-"));
        break;
      case FORMAT_REMOTE_USER:
 /* jump:798 */        if (con->authed_user->used > 1) {
          buffer_append_string_buffer(b, con->authed_user);
        } else {
          buffer_append_string_len(b, CONST_STR_LEN("-"));
        }
        break;
      case FORMAT_REQUEST_LINE:
        buffer_append_string(b, get_http_method_name(con->request.http_method));
        buffer_append_string_len(b, CONST_STR_LEN(" "));
        accesslog_append_escaped(b, con->request.orig_uri);
        buffer_append_string_len(b, CONST_STR_LEN(" "));
        buffer_append_string(b,
                             get_http_version_name(con->request.http_version));

        break;
      case FORMAT_STATUS:
        buffer_append_long(b, con->http_status);
        break;

      case FORMAT_BYTES_OUT_NO_HEADER:
 /* jump:820 */        if (con->bytes_written > 0) {
          buffer_append_off_t(b, con->bytes_written - con->bytes_header <= 0
                                     ? 0
                                     : con->bytes_written - con->bytes_header);
        } else {
          buffer_append_string_len(b, CONST_STR_LEN("-"));
        }
        break;
      case FORMAT_HEADER:
 /* jump:830 */        if (NULL !=
            (ds = (data_string *)array_get_element(
                 con->request.headers,
                 CONST_BUF_LEN(p->conf.parsed_format->ptr[j]->string)))) {
          accesslog_append_escaped(b, ds->value);
        } else {
          buffer_append_string_len(b, CONST_STR_LEN("-"));
        }
        break;
      case FORMAT_RESPONSE_HEADER:
 /* jump:840 */        if (NULL !=
            (ds = (data_string *)array_get_element(
                 con->response.headers,
                 CONST_BUF_LEN(p->conf.parsed_format->ptr[j]->string)))) {
          accesslog_append_escaped(b, ds->value);
        } else {
          buffer_append_string_len(b, CONST_STR_LEN("-"));
        }
        break;
      case FORMAT_FILENAME:
 /* jump:847 */        if (con->physical.path->used > 1) {
          buffer_append_string_buffer(b, con->physical.path);
        } else {
          buffer_append_string_len(b, CONST_STR_LEN("-"));
        }
        break;
      case FORMAT_BYTES_OUT:
 /* jump:854 */        if (con->bytes_written > 0) {
          buffer_append_off_t(b, con->bytes_written);
        } else {
          buffer_append_string_len(b, CONST_STR_LEN("-"));
        }
        break;
      case FORMAT_BYTES_IN:
 /* jump:861 */        if (con->bytes_read > 0) {
          buffer_append_off_t(b, con->bytes_read);
        } else {
          buffer_append_string_len(b, CONST_STR_LEN("-"));
        }
        break;
      case FORMAT_TIME_USED:
        buffer_append_long(b, srv->cur_ts - con->request_start);
        break;
      case FORMAT_SERVER_NAME:
 /* jump:871 */        if (con->server_name->used > 1) {
          buffer_append_string_buffer(b, con->server_name);
        } else {
          buffer_append_string_len(b, CONST_STR_LEN("-"));
        }
        break;
      case FORMAT_HTTP_HOST:
 /* jump:878 */        if (con->uri.authority->used > 1) {
          accesslog_append_escaped(b, con->uri.authority);
        } else {
          buffer_append_string_len(b, CONST_STR_LEN("-"));
        }
        break;
      case FORMAT_REQUEST_PROTOCOL:
        buffer_append_string(b, con->request.http_version == HTTP_VERSION_1_1
                                    ? "HTTP/1.1"
                                    : "HTTP/1.0");
        break;
      case FORMAT_REQUEST_METHOD:
        buffer_append_string(b, get_http_method_name(con->request.http_method));
        break;
      case FORMAT_SERVER_PORT:
        buffer_append_long(b, srv->srvconf.port);
        break;
      case FORMAT_QUERY_STRING:
        accesslog_append_escaped(b, con->uri.query);
        break;
      case FORMAT_URL:
        accesslog_append_escaped(b, con->uri.path_raw);
        break;
      case FORMAT_CONNECTION_STATUS:
        switch (con->keep_alive) {
        case 0:
          buffer_append_string_len(b, CONST_STR_LEN("-"));
          break;
        default:
          buffer_append_string_len(b, CONST_STR_LEN("+"));
          break;
        }
        break;
      default:
        /*
         { 'a', FORMAT_REMOTE_ADDR },
         { 'A', FORMAT_LOCAL_ADDR },
         { 'C', FORMAT_COOKIE },
         { 'D', FORMAT_TIME_USED_MS },
         { 'e', FORMAT_ENV },
         */

        break;
      }
      break;
    default:
      break;
    }
  }

  buffer_append_string_len(b, CONST_STR_LEN("\n"));

 /* jump:944 */  if (p->conf.use_syslog || /* syslog doesn't cache */
      (p->conf.access_logfile->used &&
       p->conf.access_logfile->ptr[0] != '|') || /* pipes don't cache */
      newts ||
      b->used > BUFFER_MAX_REUSE_SIZE) {
 /* jump:940 */    if (p->conf.use_syslog) {
#ifdef HAVE_SYSLOG_H
      if (b->used > 2) {
        /* syslog appends a \n on its own */
        syslog(LOG_INFO, "%*s", (int)b->used - 2, b->ptr);
      }
#endif
    } else if (p->conf.log_access_fd != -1) {
      write(p->conf.log_access_fd, b->ptr, b->used - 1);
    }
    buffer_reset(b);
  }

  return HANDLER_GO_ON;
}

LI_EXPORT int mod_accesslog_plugin_init(plugin *p);
LI_EXPORT int mod_accesslog_plugin_init(plugin *p) {
  p->version = LIGHTTPD_VERSION_ID;
  p->name = buffer_init_string("accesslog");

  p->init = mod_accesslog_init;
  p->set_defaults = log_access_open;
  p->cleanup = mod_accesslog_free;

  p->handle_response_done = log_access_write;
  p->handle_sighup = log_access_cycle;

  p->data = NULL;

  return 0;
}
