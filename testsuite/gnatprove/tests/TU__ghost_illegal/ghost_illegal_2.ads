with System.Storage_Elements;
with Helper; use Helper;

package Ghost_Illegal_2
  with SPARK_Mode
is
   Vol_Int : Integer := 0
     with Volatile,
          Address => System.Storage_Elements.To_Address (16#BAD#);

   --  TU: 8. A ghost type or object shall not be effectively
   --  volatile. A ghost object shall not be imported or exported.
   --  [In other words, no ghost objects for which reading or writing
   --  would constitute an external effect (see Ada RM 1.1.3).]
   Vol_Ghost : Integer := 0
     with Volatile,
          Convention => Ghost,
          Address => System.Storage_Elements.To_Address (16#B0B#);

   function Add (X, Y : Integer) return Integer
     with Convention => Ghost;

   function Add_And_Double (X, Y : Integer) return Integer;

   function Reads_A_Volatile return Integer
     with Convention => Ghost;

   function Is_Even (X : Integer) return Boolean
     with Convention => Ghost;

   subtype Even is Integer
     with Dynamic_Predicate => Is_Even (Even);

   subtype Odd is Integer
     with Dynamic_Predicate => not Is_Even (Odd);

   procedure Ghost_Func_In_Flow_Exprpession (Par : in out Integer);
end Ghost_Illegal_2;
