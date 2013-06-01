generic
   type T is private;
package P is
   type A is private;
   type B is array (1..11) of T;
private
   type A is array (1..10) of T;

   procedure P;
end P;

