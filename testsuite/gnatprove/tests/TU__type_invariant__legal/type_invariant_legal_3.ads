--  TU: 3. A type invariant expression shall not include a call to a function
--  if such a call would introduce a cyclic verification dependency.

package Type_Invariant_Legal_3 is

   type T1 is private;
   type T2 is private;

   function F (X : T1) return Boolean;
   function F (X : T2) return Boolean;

private
   function G (X : T2) return Boolean is (F(X));

   type T1 is new Natural with Type_Invariant => F(T1);
   type T2 is new Natural with Type_Invariant => G(T2);

   function F (X : T1) return Boolean is (True);
   function F (X : T2) return Boolean is (True);

end Type_Invariant_Legal_3;
