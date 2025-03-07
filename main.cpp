#include <cvc5/cvc5.h>
#include <iostream>

using namespace cvc5;

int main() {
  std::cout << "Hello, World!" << std::endl;
  TermManager tm2;
  Term t1 = tm2.mkBoolean(true);
  Term t2 = tm2.mkBoolean(false);
  std::cout << "line1: " << std::endl;
  Kind k = Kind::AND;
  try{
  tm2.mkNullableLift(k, {t1,t2});
  }catch(CVC5ApiException & e){
    std::cout << "e.what(): " << e.what() << std::endl;
  }
  std::cout << "line1: " << std::endl;
}

// Found the issue (see stack trace): `TermManager::mkNullableLift` expects `Term`s of type `Nullable T`.
// you should probably check if the `Terms`s have the correct type first before indexing their type.
// I modified the code in `SqlToSmt.lean` to make nullable values before creating the lift term.

// compilation command:
// clang++-15 main.cpp -std=c++17 -stdlib=libc++ -I .lake/build/cvc5-Linux-x86_64-static/include -L .lake/build/cvc5-Linux-x86_64-static/lib -l cvc5parser -l cvc5 -l picpolyxx -l picpoly -l cadical -l gmpxx -l gmp
// debug version:
// clang++-15 -g main.cpp -std=c++17 -stdlib=libc++ -I /home/mudathir/all/cvc5/abdoo/examples/cvc5/include -L /home/mudathir/all/cvc5/abdoo/examples/cvc5/lib -l cvc5parser -l cvc5 -l picpolyxx -l picpoly -l cadical -l gmpxx -l gmp
