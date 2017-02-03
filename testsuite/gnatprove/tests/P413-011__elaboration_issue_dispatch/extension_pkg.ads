with Root_Pkg;
pragma Elaborate_All (Root_Pkg);
package Extension_Pkg
  with Initial_Condition => Body_Elaborated
is
  pragma Elaborate_Body;
  Body_Elaborated : Boolean := False;
  type Ext is new Root_Pkg.Root with record Flag : Boolean; end record;
  overriding function Get (X : Ext) return Boolean is (Body_Elaborated);
  overriding function Op (X : Ext) return Boolean;
  Early_Call : constant Boolean :=
    Root_Pkg.Op_Wrapper (Ext'(Flag => False));
end;
