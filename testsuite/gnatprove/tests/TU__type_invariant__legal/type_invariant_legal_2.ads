--  TU: 3. Invariant checking is extended to include in-mode parameters of
--  functions in the same way as for in-mode parameters of procedures and
--  entries.

--  TU: 4. Invariant checking is extended to include checking before a call,
--  not only upon returning.

package Type_Invariant_Legal_2 is

   type T is private;

   function Pub (X : T) return Integer;
   function E_Pub (X : T) return Integer;

   procedure Pub_In (X : T);
   procedure Pub_Out (X : out T);
   procedure Pub_In_Out (X : in out T);

private
   type T is new Natural with Type_Invariant => T /= 0;

   function Priv (X : T) return Integer;
   function E_Priv (X : T) return Integer;

   function E_Pub (X : T) return Integer is (1);  --  @INVARIANT_CHECK:NONE
   function E_Priv (X : T) return Integer is (1);  --  @INVARIANT_CHECK:NONE

end Type_Invariant_Legal_2;
