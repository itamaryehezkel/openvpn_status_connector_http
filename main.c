// gcc -Wall -O2 -o ovpn_ws ovpn_ws.c
// Run as root to bind port 80: sudo ./ovpn_ws

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <time.h>
#include <errno.h>

#define OVPN_HOST      "127.0.0.1"
#define OVPN_PORT      7505
#define HTTP_PORT      80

#define MAX_BUF        65536
#define MAX_FIELDS     32
#define MAX_LINES      256
#define MAX_CLIENTS    32

struct ParsedLine {
    int field_count;
    char *fields[MAX_FIELDS];
};

struct ClientInfo {
    char name[64];
    char real[64];
    unsigned long long rx;
    unsigned long long tx;
    char since[64];
};

struct RouteInfo {
    char virtual_addr[32];
    char name[64];
    char real[64];
    char last[64];
};

struct GlobalStats {
    int max_queue;
    int has_max_queue;
};

struct StatusData {
    struct ClientInfo clients[64];
    int client_count;
    struct RouteInfo routes[64];
    int route_count;
    struct GlobalStats stats;
};

static struct StatusData g_status;

// ---------- Minimal SHA1 + Base64 for WebSocket Accept ----------

typedef struct {
    unsigned int state[5];
    unsigned int count[2];
    unsigned char buffer[64];
} SHA1_CTX;

static void SHA1Transform(unsigned int state[5], const unsigned char buffer[64]);

static void SHA1Init(SHA1_CTX* context) {
    context->state[0] = 0x67452301;
    context->state[1] = 0xEFCDAB89;
    context->state[2] = 0x98BADCFE;
    context->state[3] = 0x10325476;
    context->state[4] = 0xC3D2E1F0;
    context->count[0] = context->count[1] = 0;
}

static void SHA1Update(SHA1_CTX* context, const unsigned char* data, unsigned int len) {
    unsigned int i, j;
    j = (context->count[0] >> 3) & 63;
    if ((context->count[0] += len << 3) < (len << 3))
        context->count[1]++;
    context->count[1] += (len >> 29);
    if ((j + len) > 63) {
        memcpy(&context->buffer[j], data, (i = 64 - j));
        SHA1Transform(context->state, context->buffer);
        for (; i + 63 < len; i += 64) {
            SHA1Transform(context->state, &data[i]);
        }
        j = 0;
    } else i = 0;
    memcpy(&context->buffer[j], &data[i], len - i);
}

static void SHA1Final(unsigned char digest[20], SHA1_CTX* context) {
    unsigned int i;
    unsigned char finalcount[8];
    unsigned char c;

    for (i = 0; i < 8; i++) {
        finalcount[i] = (unsigned char)((context->count[(i >= 4 ? 0 : 1)]
            >> ((3 - (i & 3)) * 8)) & 255);
    }
    c = 0200;
    SHA1Update(context, &c, 1);
    while ((context->count[0] & 504) != 448) {
        c = 0000;
        SHA1Update(context, &c, 1);
    }
    SHA1Update(context, finalcount, 8);
    for (i = 0; i < 20; i++) {
        digest[i] = (unsigned char)
            ((context->state[i >> 2] >> ((3 - (i & 3)) * 8)) & 255);
    }
    memset(context, 0, sizeof(*context));
    memset(&finalcount, 0, sizeof(finalcount));
}

#define ROL(value, bits) (((value) << (bits)) | ((value) >> (32 - (bits))))

static void SHA1Transform(unsigned int state[5], const unsigned char buffer[64]) {
    unsigned int a, b, c, d, e;
    typedef union {
        unsigned char c[64];
        unsigned int l[16];
    } CHAR64LONG16;
    CHAR64LONG16 block[1];
    memcpy(block, buffer, 64);

    unsigned int i, j;
    unsigned int w[80];
    for (i = 0; i < 16; i++) {
        j = i * 4;
        w[i] = ((unsigned int)block->c[j] << 24) |
               ((unsigned int)block->c[j+1] << 16) |
               ((unsigned int)block->c[j+2] << 8) |
               ((unsigned int)block->c[j+3]);
    }
    for (; i < 80; i++) {
        w[i] = ROL(w[i-3] ^ w[i-8] ^ w[i-14] ^ w[i-16], 1);
    }

    a = state[0];
    b = state[1];
    c = state[2];
    d = state[3];
    e = state[4];

#define SHA1_F1(b,c,d) (((b) & (c)) | ((~b) & (d)))
#define SHA1_F2(b,c,d) ((b) ^ (c) ^ (d))
#define SHA1_F3(b,c,d) (((b) & (c)) | ((b) & (d)) | ((c) & (d)))
#define SHA1_F4(b,c,d) ((b) ^ (c) ^ (d))

#define SHA1_STEP(f, k, w) \
    do { \
        unsigned int temp = ROL(a,5) + f(b,c,d) + e + k + w; \
        e = d; d = c; c = ROL(b,30); b = a; a = temp; \
    } while (0)

    for (i = 0; i < 20; i++) SHA1_STEP(SHA1_F1, 0x5A827999, w[i]);
    for (; i < 40; i++) SHA1_STEP(SHA1_F2, 0x6ED9EBA1, w[i]);
    for (; i < 60; i++) SHA1_STEP(SHA1_F3, 0x8F1BBCDC, w[i]);
    for (; i < 80; i++) SHA1_STEP(SHA1_F4, 0xCA62C1D6, w[i]);

#undef SHA1_STEP
#undef SHA1_F1
#undef SHA1_F2
#undef SHA1_F3
#undef SHA1_F4

    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
    state[4] += e;

    memset(block, 0, sizeof(block));
}

static const char b64_table[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

static void base64_encode(const unsigned char *in, int inlen, char *out, int outlen) {
    int i;
    unsigned int v;
    char *p = out;
    (void)outlen; // not strictly used for brevity

    for (i = 0; i < inlen; i += 3) {
        v = in[i];
        v = (v << 8) | (i+1 < inlen ? in[i+1] : 0);
        v = (v << 8) | (i+2 < inlen ? in[i+2] : 0);
        *p++ = b64_table[(v >> 18) & 0x3F];
        *p++ = b64_table[(v >> 12) & 0x3F];
        *p++ = (i+1 < inlen) ? b64_table[(v >> 6) & 0x3F] : '=';
        *p++ = (i+2 < inlen) ? b64_table[v & 0x3F] : '=';
    }
    *p = '\0';
}

// ---------- WebSocket helpers ----------

static int websocket_send_text(int fd, const char *msg) {
    size_t len = strlen(msg);
    unsigned char header[10];
    size_t hlen = 0;

    header[0] = 0x81; // FIN + text
    if (len <= 125) {
        header[1] = (unsigned char)len;
        hlen = 2;
    } else if (len <= 65535) {
        header[1] = 126;
        header[2] = (len >> 8) & 0xFF;
        header[3] = len & 0xFF;
        hlen = 4;
    } else {
        header[1] = 127;
        header[2] = header[3] = header[4] = header[5] = 0;
        header[6] = (len >> 24) & 0xFF;
        header[7] = (len >> 16) & 0xFF;
        header[8] = (len >> 8) & 0xFF;
        header[9] = len & 0xFF;
        hlen = 10;
    }

    if (write(fd, header, hlen) != (ssize_t)hlen) return -1;
    if (write(fd, msg, len) != (ssize_t)len) return -1;
    return 0;
}

// ---------- Embedded HTML ----------

static const char *html_page =
"HTTP/1.1 200 OK\r\n"
"Content-Type: text/html; charset=utf-8\r\n"
"Connection: close\r\n"
"\r\n"
"<!DOCTYPE html>\n"
"<html>\n"
"<head>\n"
"<meta charset=\"utf-8\" />\n"
"<title>OpenVPN Status</title>\n"
"<style>\n"
"body { background:#111; color:#eee; font-family: monospace; }\n"
"table { border-collapse: collapse; margin-top:10px; }\n"
"th, td { border:1px solid #444; padding:4px 8px; }\n"
"th { background:#222; }\n"
".section { margin-top:20px; }\n"
"</style>\n"
"</head>\n"
"<body>\n"
"<h1>OpenVPN Status</h1>\n"
"<div id=\"status\">Connecting...</div>\n"
"<div class=\"section\">\n"
"<h2>Clients</h2>\n"
"<table id=\"clients\"><thead><tr>\n"
"<th>Name</th><th>Real</th><th>RX</th><th>TX</th><th>Since</th>\n"
"</tr></thead><tbody></tbody></table>\n"
"</div>\n"
"<div class=\"section\">\n"
"<h2>Routes</h2>\n"
"<table id=\"routes\"><thead><tr>\n"
"<th>Virtual</th><th>Name</th><th>Real</th><th>Last</th>\n"
"</tr></thead><tbody></tbody></table>\n"
"</div>\n"
"<div class=\"section\">\n"
"<h2>Global Stats</h2>\n"
"<pre id=\"stats\"></pre>\n"
"</div>\n"
"<script>\n"
"function $(id){return document.getElementById(id);}\n"
"let ws = new WebSocket((location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + '/ws');\n"
"ws.onopen = () => { $('status').textContent = 'Connected'; };\n"
"ws.onclose = () => { $('status').textContent = 'Disconnected'; };\n"
"ws.onerror = () => { $('status').textContent = 'Error'; };\n"
"ws.onmessage = (ev) => {\n"
"  try {\n"
"    const data = JSON.parse(ev.data);\n"
"    const cbody = $('clients').querySelector('tbody');\n"
"    const rbody = $('routes').querySelector('tbody');\n"
"    cbody.innerHTML = '';\n"
"    rbody.innerHTML = '';\n"
"    (data.clients || []).forEach(c => {\n"
"      const tr = document.createElement('tr');\n"
"      ['name','real','rx','tx','since'].forEach(k => {\n"
"        const td = document.createElement('td');\n"
"        td.textContent = c[k];\n"
"        tr.appendChild(td);\n"
"      });\n"
"      cbody.appendChild(tr);\n"
"    });\n"
"    (data.routes || []).forEach(r => {\n"
"      const tr = document.createElement('tr');\n"
"      ['virtual','name','real','last'].forEach(k => {\n"
"        const td = document.createElement('td');\n"
"        td.textContent = r[k];\n"
"        tr.appendChild(td);\n"
"      });\n"
"      rbody.appendChild(tr);\n"
"    });\n"
"    let s = '';\n"
"    if (data.stats && typeof data.stats.max_queue !== 'undefined') {\n"
"      s += 'Max bcast/mcast queue length: ' + data.stats.max_queue + '\\n';\n"
"    }\n"
"    $('stats').textContent = s;\n"
"  } catch(e) {\n"
"    console.error(e);\n"
"  }\n"
"};\n"
"</script>\n"
"</body>\n"
"</html>\n";

// ---------- OpenVPN parsing ----------

static void parse_ovpn_status(const char *buf) {
    struct ParsedLine lines[MAX_LINES];
    int line_count = 0;

    char tmp[MAX_BUF];
    strncpy(tmp, buf, sizeof(tmp)-1);
    tmp[sizeof(tmp)-1] = 0;

    char *saveptr1;
    char *line = strtok_r(tmp, "\n", &saveptr1);

    while (line && line_count < MAX_LINES) {
        size_t len = strlen(line);
        if (len > 0 && line[len-1] == '\r')
            line[len-1] = '\0';

        struct ParsedLine *pl = &lines[line_count];
        pl->field_count = 0;

        char *saveptr2;
        char *field = strtok_r(line, ",", &saveptr2);
        while (field && pl->field_count < MAX_FIELDS) {
            pl->fields[pl->field_count++] = field;
            field = strtok_r(NULL, ",", &saveptr2);
        }

        line_count++;
        line = strtok_r(NULL, "\n", &saveptr1);
    }

    g_status.client_count = 0;
    g_status.route_count = 0;
    g_status.stats.has_max_queue = 0;

    int mode = 0;
    for (int i = 0; i < line_count; i++) {
        struct ParsedLine *pl = &lines[i];
        if (pl->field_count == 0) continue;

        if (strcmp(pl->fields[0], "OpenVPN CLIENT LIST") == 0) {
            mode = 1;
            continue;
        }
        if (strcmp(pl->fields[0], "ROUTING TABLE") == 0) {
            mode = 2;
            continue;
        }
        if (strcmp(pl->fields[0], "GLOBAL STATS") == 0) {
            mode = 3;
            continue;
        }
        if (strcmp(pl->fields[0], "END") == 0) {
            mode = 0;
            continue;
        }

        if (mode == 1 && pl->field_count == 5) {
            if (g_status.client_count < (int)(sizeof(g_status.clients)/sizeof(g_status.clients[0]))) {
                struct ClientInfo *c = &g_status.clients[g_status.client_count++];
                strncpy(c->name, pl->fields[0], sizeof(c->name)-1);
                strncpy(c->real, pl->fields[1], sizeof(c->real)-1);
                c->rx = strtoull(pl->fields[2], NULL, 10);
                c->tx = strtoull(pl->fields[3], NULL, 10);
                strncpy(c->since, pl->fields[4], sizeof(c->since)-1);
            }
        } else if (mode == 2 && pl->field_count == 4) {
            if (g_status.route_count < (int)(sizeof(g_status.routes)/sizeof(g_status.routes[0]))) {
                struct RouteInfo *r = &g_status.routes[g_status.route_count++];
                strncpy(r->virtual_addr, pl->fields[0], sizeof(r->virtual_addr)-1);
                strncpy(r->name, pl->fields[1], sizeof(r->name)-1);
                strncpy(r->real, pl->fields[2], sizeof(r->real)-1);
                strncpy(r->last, pl->fields[3], sizeof(r->last)-1);
            }
        } else if (mode == 3 && pl->field_count == 2) {
            if (strcmp(pl->fields[0], "Max bcast/mcast queue length") == 0) {
                g_status.stats.max_queue = atoi(pl->fields[1]);
                g_status.stats.has_max_queue = 1;
            }
        }
    }
}

// ---------- JSON builder ----------

static void build_status_json(char *out, size_t outsz) {
    char *p = out;
    size_t left = outsz;

    int n = snprintf(p, left, "{ \"clients\": [");
    if (n < 0 || (size_t)n >= left) { out[0] = 0; return; }
    p += n; left -= n;

    for (int i = 0; i < g_status.client_count; i++) {
        struct ClientInfo *c = &g_status.clients[i];
        n = snprintf(p, left,
            "%s{\"name\":\"%s\",\"real\":\"%s\",\"rx\":%llu,\"tx\":%llu,\"since\":\"%s\"}",
            (i == 0 ? "" : ","),
            c->name, c->real,
            (unsigned long long)c->rx,
            (unsigned long long)c->tx,
            c->since
        );
        if (n < 0 || (size_t)n >= left) { out[0] = 0; return; }
        p += n; left -= n;
    }

    n = snprintf(p, left, "],\"routes\":[");
    if (n < 0 || (size_t)n >= left) { out[0] = 0; return; }
    p += n; left -= n;

    for (int i = 0; i < g_status.route_count; i++) {
        struct RouteInfo *r = &g_status.routes[i];
        n = snprintf(p, left,
            "%s{\"virtual\":\"%s\",\"name\":\"%s\",\"real\":\"%s\",\"last\":\"%s\"}",
            (i == 0 ? "" : ","),
            r->virtual_addr, r->name, r->real, r->last
        );
        if (n < 0 || (size_t)n >= left) { out[0] = 0; return; }
        p += n; left -= n;
    }

    n = snprintf(p, left, "],\"stats\":{");
    if (n < 0 || (size_t)n >= left) { out[0] = 0; return; }
    p += n; left -= n;

    int first = 1;
    if (g_status.stats.has_max_queue) {
        n = snprintf(p, left, "%s\"max_queue\":%d",
                     first ? "" : ",", g_status.stats.max_queue);
        if (n < 0 || (size_t)n >= left) { out[0] = 0; return; }
        p += n; left -= n;
        first = 0;
    }

    n = snprintf(p, left, "}}");
    if (n < 0 || (size_t)n >= left) { out[0] = 0; return; }
    p += n; left -= n;
}

// ---------- HTTP/WebSocket server ----------

struct WsClient {
    int fd;
    int active;
};

static struct WsClient ws_clients[MAX_CLIENTS];

static void add_ws_client(int fd) {
    for (int i = 0; i < MAX_CLIENTS; i++) {
        if (!ws_clients[i].active) {
            ws_clients[i].fd = fd;
            ws_clients[i].active = 1;
            return;
        }
    }
    close(fd);
}

static void remove_ws_client(int i) {
    if (ws_clients[i].active) {
        close(ws_clients[i].fd);
        ws_clients[i].active = 0;
    }
}

static void broadcast_status_json(void) {
    char json[8192];
    build_status_json(json, sizeof(json));
    if (json[0] == 0) return;

    for (int i = 0; i < MAX_CLIENTS; i++) {
        if (ws_clients[i].active) {
            if (websocket_send_text(ws_clients[i].fd, json) < 0) {
                remove_ws_client(i);
            }
        }
    }
}

static int handle_http_request(int fd) {
    char buf[4096];
    ssize_t n = recv(fd, buf, sizeof(buf)-1, 0);
    if (n <= 0) return -1;
    buf[n] = 0;

    if (strncmp(buf, "GET / ", 6) == 0) {
        send(fd, html_page, strlen(html_page), 0);
        return -1;
    }

    if (strncmp(buf, "GET /ws", 7) == 0) {
        char *key_hdr = strcasestr(buf, "Sec-WebSocket-Key:");
        if (!key_hdr) return -1;
        key_hdr += strlen("Sec-WebSocket-Key:");
        while (*key_hdr == ' ' || *key_hdr == '\t') key_hdr++;
        char *end = strstr(key_hdr, "\r\n");
        if (!end) return -1;
        char key[128];
        size_t klen = end - key_hdr;
        if (klen >= sizeof(key)) return -1;
        memcpy(key, key_hdr, klen);
        key[klen] = 0;

        const char *guid = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
        char concat[256];
        snprintf(concat, sizeof(concat), "%s%s", key, guid);

        unsigned char sha[20];
        SHA1_CTX ctx;
        SHA1Init(&ctx);
        SHA1Update(&ctx, (unsigned char*)concat, strlen(concat));
        SHA1Final(sha, &ctx);

        char accept[128];
        base64_encode(sha, 20, accept, sizeof(accept));

        char resp[512];
        int rn = snprintf(resp, sizeof(resp),
            "HTTP/1.1 101 Switching Protocols\r\n"
            "Upgrade: websocket\r\n"
            "Connection: Upgrade\r\n"
            "Sec-WebSocket-Accept: %s\r\n"
            "\r\n", accept);
        if (rn <= 0 || rn >= (int)sizeof(resp)) return -1;
        send(fd, resp, rn, 0);

        add_ws_client(fd);
        return 0;
    }

    const char *resp =
        "HTTP/1.1 404 Not Found\r\n"
        "Content-Length: 0\r\n"
        "Connection: close\r\n"
        "\r\n";
    send(fd, resp, strlen(resp), 0);
    return -1;
}

// ---------- Main ----------

int main(int argc, char *argv[]) {
    int interval = 3;
    if (argc > 1) interval = atoi(argv[1]);
    if (interval <= 0) interval = 3;

    memset(&g_status, 0, sizeof(g_status));
    memset(ws_clients, 0, sizeof(ws_clients));

    int ovpn_sock = socket(AF_INET, SOCK_STREAM, 0);
    if (ovpn_sock < 0) { perror("socket ovpn"); return 1; }

    struct sockaddr_in ovpn_addr = {0};
    ovpn_addr.sin_family = AF_INET;
    ovpn_addr.sin_port = htons(OVPN_PORT);
    inet_pton(AF_INET, OVPN_HOST, &ovpn_addr.sin_addr);

    if (connect(ovpn_sock, (struct sockaddr*)&ovpn_addr, sizeof(ovpn_addr)) < 0) {
        perror("connect ovpn");
        return 1;
    }

    int http_sock = socket(AF_INET, SOCK_STREAM, 0);
    if (http_sock < 0) { perror("socket http"); return 1; }

    int opt = 1;
    setsockopt(http_sock, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));

    struct sockaddr_in http_addr = {0};
    http_addr.sin_family = AF_INET;
    http_addr.sin_port = htons(HTTP_PORT);
    inet_pton(AF_INET, "10.8.0.1", &http_addr.sin_addr);

    if (bind(http_sock, (struct sockaddr*)&http_addr, sizeof(http_addr)) < 0) {
        perror("bind http");
        return 1;
    }

    if (listen(http_sock, 16) < 0) {
        perror("listen http");
        return 1;
    }

    printf("Connected to OpenVPN at %s:%d\n", OVPN_HOST, OVPN_PORT);
    printf("HTTP/WebSocket server listening on 10.8.0.1:%d\n", HTTP_PORT);

    const char *status_cmd = "status\n";
    time_t last = 0;

    char ovpn_buf[MAX_BUF];
    int ovpn_len = 0;

    while (1) {
        fd_set rfds;
        FD_ZERO(&rfds);
        FD_SET(ovpn_sock, &rfds);
        FD_SET(http_sock, &rfds);
        int maxfd = (ovpn_sock > http_sock ? ovpn_sock : http_sock);

        for (int i = 0; i < MAX_CLIENTS; i++) {
            if (ws_clients[i].active) {
                FD_SET(ws_clients[i].fd, &rfds);
                if (ws_clients[i].fd > maxfd) maxfd = ws_clients[i].fd;
            }
        }

        struct timeval tv;
        tv.tv_sec = 1;
        tv.tv_usec = 0;

        int r = select(maxfd+1, &rfds, NULL, NULL, &tv);
        if (r < 0) {
            if (errno == EINTR) continue;
            perror("select");
            break;
        }

        time_t now = time(NULL);
        if (now - last >= interval) {
            send(ovpn_sock, status_cmd, strlen(status_cmd), 0);
            last = now;
        }

        if (FD_ISSET(ovpn_sock, &rfds)) {
            char buf[2048];
            ssize_t n = recv(ovpn_sock, buf, sizeof(buf)-1, 0);
            if (n <= 0) {
                printf("OpenVPN connection closed\n");
                break;
            }
            buf[n] = 0;
            if (ovpn_len + n < (int)sizeof(ovpn_buf)) {
                memcpy(ovpn_buf + ovpn_len, buf, n);
                ovpn_len += n;
                ovpn_buf[ovpn_len] = 0;
            }

            if (strstr(ovpn_buf, "\nEND\r\n") || strstr(ovpn_buf, "\nEND\n")) {
                parse_ovpn_status(ovpn_buf);
                broadcast_status_json();
                ovpn_len = 0;
            }
        }

        if (FD_ISSET(http_sock, &rfds)) {
            struct sockaddr_in cli_addr;
            socklen_t cli_len = sizeof(cli_addr);
            int cfd = accept(http_sock, (struct sockaddr*)&cli_addr, &cli_len);
            if (cfd >= 0) {
                if (handle_http_request(cfd) < 0) {
                    close(cfd);
                }
            }
        }

        for (int i = 0; i < MAX_CLIENTS; i++) {
            if (ws_clients[i].active && FD_ISSET(ws_clients[i].fd, &rfds)) {
                char tmp[512];
                ssize_t n = recv(ws_clients[i].fd, tmp, sizeof(tmp), 0);
                if (n <= 0) {
                    remove_ws_client(i);
                }
            }
        }
    }

    close(ovpn_sock);
    close(http_sock);
    return 0;
}
