#include "stdlib.h"
#include "stringBuffers.h"
#include "threading.h"
#include "sockets.h"

struct email {
  struct string_buffer* body;
  struct email* next;
};

struct account {
  struct string_buffer* username;
  struct string_buffer* password;
  struct email* inbox;
  int nb_messages;
  struct account* next;
};

struct database {
  struct account* head;
  struct mutex* mutex;
};

/*@
predicate emails(struct email* email; int depth) =
  email == 0 ?
    depth == 0
  :
    malloc_block_email(email)
    &*& email->body |-> ?body &*& string_buffer(body)
    &*& email->next |-> ?next
    &*& emails(next, ?lower_depth)
    &*& depth == lower_depth + 1;

predicate accounts(struct account* a; int depth) =
  a == 0 ?
    depth == 0
  :
    malloc_block_account(a)
    &*& a->username |-> ?username &*& string_buffer(username)
    &*& a->password |-> ?password &*& string_buffer(password)
    &*& a->nb_messages |-> ?nb_messages &*& 0 <= nb_messages
    &*& a->inbox |-> ?inbox &*& emails(inbox, nb_messages)
    &*& a->next |-> ?next
    &*& accounts(next, ?lower_depth)
    &*& depth == lower_depth + 1;

predicate_ctor database_pre(struct database* db)() =
  db->head |-> ?head
  &*& accounts(head, ?depth);

predicate database(struct database* db; int count) =
  malloc_block_database(db)
  &*& db->head |-> ?head
  &*& count >= 0
  &*& accounts(head, count)
  &*& [_]db->mutex |-> ?mutex
  &*& [_]mutex(mutex, database_pre(db));

predicate_family_instance thread_run_data(handle_connection)(struct session* ss) =
  // Overloading a predicate:
  // takes function pointer as index
  // different definiton for different function pointer  
  malloc_block_session(ss)
  &*& ss->socket |-> ?sock
  &*& socket(sock)
  &*& ss->db |-> ?db
  &*& [_]db->mutex |-> ?mutex
  &*& [_]mutex(mutex, database_pre(db));
@*/


void account_dispose(struct account* a)
{
  struct email* curr = a->inbox;
  while(curr != 0)
  {
    struct email* tmp = curr->next;
    string_buffer_dispose(curr->body);
    free(curr);
    curr = tmp;
  }
  string_buffer_dispose(a->username);
  string_buffer_dispose(a->password);
  free(a);
}

bool accounts_contains(struct account* a, struct string_buffer* username)
//@ requires accounts(a, ?depth) &*& string_buffer(username);
//@ ensures accounts(a, depth) &*& string_buffer(username);
{
  if(a == 0) {
    return false;
  } else {
    bool found = string_buffer_equals(a->username, username);
    if(found) {
      return true;
    } else {
      return accounts_contains(a->next, username);
    }
  }
}

int create_account(struct database* db, struct string_buffer* username, struct string_buffer* password)
/*@ requires
  [_]db->mutex |-> ?mutex //Only a fraction of a mutex chunk is required to acquire the mutex
  &*& [_]mutex(mutex, database_pre(db))
  &*& string_buffer(username)
  &*& string_buffer(password);
@*/
/*@ ensures
  [_]db->mutex |-> mutex
  &*& [_]mutex(mutex, database_pre(db))
  &*& result == 0 ?
    true
    :
    (string_buffer(username)
    &*& string_buffer(password));
@*/
{
  bool username_taken;
  struct account* a = malloc(sizeof(struct account));
  if(a == 0) return -1;
  a->username = username;
  a->password = password;
  a->inbox = 0;
  a->nb_messages = 0;

  mutex_acquire(db->mutex);
  //@ open database_pre(db)();
  
  username_taken = accounts_contains(db->head, username);
  if(username_taken) {
    //@ close database_pre(db)();
    mutex_release(db->mutex);
    free(a);
    return -2;
  }

  a->next = db->head;
  db->head = a;

  //@ close database_pre(db)();
  mutex_release(db->mutex);
  return 0;
}

int send_mail_core(struct account* a, struct string_buffer* to, struct email* e)
/*@ requires
  string_buffer(to)
  &*& accounts(a, _)
  &*& e != 0
  &*& malloc_block_email(e)
  &*& e->body |-> ?body &*& string_buffer(body)
  &*& e->next |-> _;
@*/
/*@ ensures
string_buffer(to)
&*& accounts(a, _)
&*& result == 0 ?
    true
    :
    malloc_block_email(e)
    &*& e->body |-> body &*& string_buffer(body)
    &*& e->next |-> _;
@*/
{
  if(a == 0) {
    return -2;
  } else {
    bool found = string_buffer_equals(a->username, to);
    if(found) {
      if(a->nb_messages <= 1000) {
        e->next = a->inbox;
        a->inbox = e;
        a->nb_messages = a->nb_messages + 1;
        return 0;
      } else {
        return -3;
      }
    } else {
      return send_mail_core(a->next, to, e);
    }
  }
}

int send_mail(struct database* db, struct string_buffer* to, struct string_buffer* body)
/*@ requires
  [_]db->mutex |-> ?mutex
  &*& [_]mutex(mutex, database_pre(db))
  &*& string_buffer(to)
  &*& string_buffer(body);
@*/
/*@ ensures
  [_]db->mutex |-> mutex
  &*& [_]mutex(mutex, database_pre(db))
  &*& result == 0 ?
    true
    :
    string_buffer(to)
    &*& string_buffer(body);
@*/{
  int res;
  struct email* e = malloc(sizeof(struct email));
  if(e == 0) return -1;
  e->body = body;

  mutex_acquire(db->mutex);
  //@ open database_pre(db)();
  res = send_mail_core(db->head, to, e);
  //@ close database_pre(db)();
  mutex_release(db->mutex);
  if(res != 0) {
    free(e);
  } else {
    string_buffer_dispose(to);
  }
  return res;

}

void write_mails_to_buffer(struct email* e, struct string_buffer* buf)
//@ requires emails(e, ?depth) &*& string_buffer(buf);
//@ ensures emails(e, depth) &*& string_buffer(buf);
{
  if(e == 0) {
  } else {
    write_mails_to_buffer(e->next, buf);
    string_buffer_append_string_buffer(buf, e->body);
    string_buffer_append_string(buf, "\r\n");
  }
  ;
}

int read_mail_core(struct account* a, struct string_buffer* buf, struct string_buffer* username, struct string_buffer* password)
/*@ requires
  string_buffer(buf)
  &*& string_buffer(username)
  &*& string_buffer(password)
  &*& accounts(a, ?depth);
@*/
/*@ ensures
  string_buffer(buf)
  &*& string_buffer(username)
  &*& string_buffer(password)
  &*& accounts(a, depth);
@*/
{
  if(a == 0) {
    return -1;
  } else {
    bool found = string_buffer_equals(a->username, username);
    if(found) {
      bool password_correct = string_buffer_equals(a->password, password);
      if(password_correct) {
        string_buffer_append_string(buf, "You have ");
        string_buffer_append_integer_as_decimal(buf, a->nb_messages);
        string_buffer_append_string(buf, " messages:\r\n");
        write_mails_to_buffer(a->inbox, buf);
        return 0;
      } else {
        return -2;
      }
    } else {
      return read_mail_core(a->next, buf, username, password);
    }
  }
}

int read_mail(struct database* db, struct string_buffer* output, struct string_buffer* username, struct string_buffer* password)
/*@ requires
  [_]db->mutex |-> ?mutex
  &*& [_]mutex(mutex, database_pre(db))
  &*& string_buffer(output)
  &*& string_buffer(username)
  &*& string_buffer(password);
@*/
/*@ ensures
  [_]db->mutex |-> mutex
  &*& [_]mutex(mutex, database_pre(db))
  &*& string_buffer(output)
  &*& string_buffer(username)
  &*& string_buffer(password);
@*/
{
  int res;

  mutex_acquire(db->mutex);
  //@ open database_pre(db)();
  res = read_mail_core(db->head, output, username, password);
  //@ close database_pre(db)();
  mutex_release(db->mutex);

  return res;
}

void show_user_names(struct database* db, struct string_buffer* buf)
/*@ requires
  [_]db->mutex |-> ?mutex
  &*& [_]mutex(mutex, database_pre(db))
  &*& string_buffer(buf);
@*/
/*@ ensures
  [_]db->mutex |-> mutex
  &*& [_]mutex(mutex, database_pre(db))
  &*& string_buffer(buf);
@*/
{
  struct account* curr;

  mutex_acquire(db->mutex);
  //@ open database_pre(db)();
  curr = db->head;
  while(curr != 0) // Hint: consider using a loop contract
  //@ requires accounts(curr, ?depth) &*& string_buffer(buf);
  //@ ensures accounts(old_curr, depth) &*& string_buffer(buf);
  {
    string_buffer_append_string_buffer(buf, curr->username);
    string_buffer_append_string(buf, "\r\n");
    curr = curr->next;
    //@ recursive_call();
  }

  //@ close database_pre(db)();
  mutex_release(db->mutex);
}

void show_menu(struct socket* s)
//@ requires socket(s);
//@ ensures socket(s);
{
  socket_write_string(s, "1. create account\r\n");
  socket_write_string(s, "2. send mail\r\n");
  socket_write_string(s, "3. read mail\r\n");
  socket_write_string(s, "4. show all user names\r\n");
  socket_write_string(s, "5. quit\r\n");
}

void main_menu(struct socket* s, struct database* db)
/*@ requires
  socket(s)
  &*& [_]db->mutex |-> ?mutex
  &*& [_]mutex(mutex, database_pre(db));
@*/
/*@ ensures
  [_]db->mutex |-> mutex
  &*& [_]mutex(mutex, database_pre(db));
@*/
{
  int choice;
  socket_write_string(s, "welcome!\r\n");
  show_menu(s);
  choice = socket_read_nonnegative_integer(s);
  while(choice != 5)
  /*@ invariant
    socket(s)
    &*& [_]db->mutex |-> mutex
    &*& [_]mutex(mutex, database_pre(db));
  @*/
  {
    int res;
    if(choice == 1) {
      struct string_buffer* username = create_string_buffer();
      struct string_buffer* password = create_string_buffer();
      socket_write_string(s, "enter username\r\n");
      socket_read_line(s, username);
      socket_write_string(s, "enter password\r\n");
      socket_read_line(s, password);

      res = create_account(db, username, password);
      if(res == 0) {
        socket_write_string(s, "account created\r\n");
      } else {
        string_buffer_dispose(username);
        string_buffer_dispose(password);
        if(res == -1) {
          socket_write_string(s, "insufficient memory\r\n");
        } else {
          socket_write_string(s, "username already in use\r\n");
        }
      }
    } else if(choice == 2) {
      struct string_buffer* to = create_string_buffer();
      struct string_buffer* body = create_string_buffer();
      socket_write_string(s, "enter to\r\n");
      socket_read_line(s, to);
      socket_write_string(s, "enter body\r\n");
      socket_read_line(s, body);
      res = send_mail(db, to, body);
      if(res == 0) {
        socket_write_string(s, "mail sent\r\n");
      } else {
        string_buffer_dispose(body);
        string_buffer_dispose(to);
        if(res == -1) {
          socket_write_string(s, "insufficient memory\r\n");
        } else if(res == -2) {
          socket_write_string(s, "user not found\r\n");
        } else {
          socket_write_string(s, "user inbox full\r\n");
        }
      }
    } else if(choice == 3) {
      struct string_buffer* username = create_string_buffer();
      struct string_buffer* password = create_string_buffer();
      struct string_buffer* buf = create_string_buffer();
      socket_write_string(s, "enter username\r\n");
      socket_read_line(s, username);
      socket_write_string(s, "enter password\r\n");
      socket_read_line(s, password);
      res = read_mail(db, buf, username, password);
      if(res == 0) {
        socket_write_string_buffer(s, buf);
      } else if(res == -1) {
        socket_write_string(s, "bad username\r\n");
      } else {
        socket_write_string(s, "wrong password\r\n");
      }
      string_buffer_dispose(username);
      string_buffer_dispose(password);
      string_buffer_dispose(buf);
    } else if(choice == 4) {
      struct string_buffer* buf = create_string_buffer();
      show_user_names(db, buf);
      socket_write_string_buffer(s, buf);
      string_buffer_dispose(buf);
    } else {
      socket_write_string(s, "invalid choice, try again\r\n");
    }
    show_menu(s);
    choice = socket_read_nonnegative_integer(s);
  }
  socket_write_string(s, "bye!\r\n");
  socket_close(s);
}

struct session {
  struct socket* socket;
  struct database* db;
};

void handle_connection(struct session* session)//@ : thread_run
//@ requires thread_run_data(handle_connection)(session);
//@ ensures true;
{
  //@ open thread_run_data(handle_connection)(session);
  main_menu(session->socket, session->db);
  free(session);
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  struct server_socket* ss;
  struct mutex* mutex;
  struct database* db = malloc(sizeof(struct database));
  if(db == 0) abort();
  db->head = 0;

  //@ close database_pre(db)(); //lock invariant that specifies the memory locations that will be owned by the mutex
  //@ close create_mutex_ghost_arg(database_pre(db)); //p.51
  mutex = create_mutex();
  db->mutex = mutex;
  //@ leak db->mutex |-> mutex &*& mutex(mutex, _); // p.97
  
  ss = create_server_socket(1234);
  
  while(true)
  /*@ invariant
    server_socket(ss)
    &*& [_]db->mutex |-> mutex
    &*& [_]mutex(mutex, database_pre(db));
  @*/ // p.97
  {
    struct socket* s = server_socket_accept(ss);
    struct session* session = malloc(sizeof(struct session));
    if(session == 0) {
      socket_write_string(s, "insufficient memory\r\n");
      socket_close(s);
    } else {
      session->socket = s;
      session->db = db;
      
      //@ close thread_run_data(handle_connection)(session);
      thread_start(handle_connection, session);
    }
  } 
}
