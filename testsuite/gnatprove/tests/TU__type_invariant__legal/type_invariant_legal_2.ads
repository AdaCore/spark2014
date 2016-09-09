--  TU: 3. Invariant checking is extended to include in-mode parameters of
--  functions in the same way as for in-mode parameters of procedures and
--  entries.

--  TU: 4. Invariant checking is extended to include checking before a call,
--  not only upon returning.

package Type_Invariant_Legal_2 with SPARK_Mode is

   type T is private;

   function Pub (X : T) return Integer;  --  @INVARIANT_CHECK:NONE
   function E_Pub (X : T) return Integer;  --  @INVARIANT_CHECK:NONE

   procedure Pub_In (X : T);  --  @INVARIANT_CHECK:NONE
   procedure Pub_Out (X : out T);  --  @INVARIANT_CHECK:PASS
   procedure Pub_In_Out (X : in out T);  --  @INVARIANT_CHECK:PASS

private
   type T is new Natural with Type_Invariant => T /= 0;

   function Priv (X : T) return Integer with Pre => True;  --  @INVARIANT_CHECK:NONE
   function E_Priv (X : T) return Integer;  --  @INVARIANT_CHECK:NONE

   function E_Pub (X : T) return Integer is (1);
   function E_Priv (X : T) return Integer is (1);

end Type_Invariant_Legal_2;
