with Simple_Private_Type; use Simple_Private_Type;
package Use_Simple_Private_Type with SPARK_Mode is
   type T is new My_Int;
   type U is private;
   subtype S is My_Int;

   function Add (X, Y : T) return T;

   procedure Add (X : in out U; Y : U);

   function Mul (X, Y : T) return T;

   procedure Mul (X : in out U; Y : U);
private
   type U is new My_Int;
end Use_Simple_Private_Type;
