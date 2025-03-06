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