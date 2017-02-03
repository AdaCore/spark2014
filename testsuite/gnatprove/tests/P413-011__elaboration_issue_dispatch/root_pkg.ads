limited with Extension_Pkg;
package Root_Pkg with Elaborate_Body is
   type Root is abstract tagged null record;
   function Get (X : Root) return Boolean is (True) with
     Global => (Input => Extension_Pkg.Body_Elaborated);
   function Op (X : Root) return Boolean with
     Global => (Proof_In => Extension_Pkg.Body_Elaborated),
     Pre'Class => X.Get;
   function Op_Wrapper (Y : Root'Class) return Boolean with
     Pre => Y.Get;
end;
