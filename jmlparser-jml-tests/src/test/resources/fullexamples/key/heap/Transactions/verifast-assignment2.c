#include "stdlib.h"

struct transaction {
  int amount;
  struct transaction* next;
};

struct account {
  struct transaction* transactions;
};

/*@
predicate trans(struct transaction* t; int sum) =
   t == 0 ? 
     (sum == 0) :
     (t->amount |-> ?s &*& malloc_block_transaction(t) &*&
       t->next |-> ?n &*& trans(n, ?tail) &*& sum == s + tail);
     
predicate account(struct account* a; int balance) = 
   malloc_block_account(a) &*& account_transactions(a, ?t) &*& trans(t, balance);
   
@*/

struct account* account_create() 
  //@ requires true;
  //@ ensures result == 0 ? true : account(result, 0); 
{
  struct account* a = malloc(sizeof(struct account));
  if(a == 0) return 0;
  a->transactions = 0;
  return a;
  //@ close trans(0,0);
  //@ close account(a,0);
}

void account_deposit(struct account* a, int amount)
  //@ requires account(a, ?balance) &*& 0 <= amount;
  //@ ensures account(a, balance + amount); 
{
  assert(0<=amount);
  struct transaction* t = malloc(sizeof(struct transaction));
  if(t == 0) abort();
  t->amount = amount;
  t->next = a->transactions;
  a->transactions = t;
}

void account_withdraw(struct account* a, int amount)
  //@ requires account(a, ?balance) &*& 0 <= amount &*& 0 <= balance - amount;
  //@ ensures account(a, balance - amount); 
{
  assert(0<=amount);
  struct transaction* t = malloc(sizeof(struct transaction));
  if(t == 0) abort();
  t->amount = -amount;
  t->next = a->transactions;
  a->transactions = t;
}

int transactions_get_total(struct transaction* t)
  //@ requires trans(t, ?s);
  //@ ensures result == s &*& trans(t, s);
{
  //@ open trans(t, ?ss);
  if(t == 0) {
    return 0;
  } else {
    int tmp = transactions_get_total(t->next);
    return t->amount + tmp;
  }
}

int account_get_balance(struct account* a)
  //@ requires account(a, ?balance);
  //@ ensures account(a, balance) &*& result == balance;
{
  return transactions_get_total(a->transactions);
}

void account_transfer(struct account* from, struct account* to, int amount)
  //@ requires account(from, ?fbalance) &*& account(to, ?tbalance) &*& 0 <= amount &*& 0 <= fbalance - amount;
  //@ ensures account(from, fbalance - amount) &*& account(to, tbalance + amount);
{
  account_withdraw(from, amount);
  account_deposit(to, amount);
}

void account_dispose(struct account* a)
  //@ requires account(a, _) &*& account(a,_);
  //@ ensures true &*& account(a,_);
{
  struct transaction* current = a->transactions;
  while(current != 0) 
    //@ invariant current == 0 ? true : trans(current, _);
  {
    struct transaction* tmp = current->next;
    free(current);
    current = tmp;
  }
  free(a);
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  struct account* a1 = account_create();
  if(a1 == 0) { 
    return -1;
  }
  account_deposit(a1, 100);
  struct account* a2 = account_create();
  if(a2 == 0) {
    account_dispose(a1);
    return -1;
  }
  account_deposit(a2, 200);
  account_transfer(a1, a2, 50);
  int tmp = account_get_balance(a2);
  assert(tmp == 250);
  account_dispose(a1);
  account_dispose(a2);
  return 0;
}