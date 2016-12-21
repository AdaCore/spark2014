with Root_Pkg;
pragma Elaborate_All (Root_Pkg);
package Extension_Pkg is
  Body_Elaborated : Boolean := False;
  type Ext is new Root_Pkg.Root with record Flag : Boolean; end record;
  overriding function Op (X : Ext) return Boolean;
  Early_Call : constant Boolean :=
    Root_Pkg.Op_Wrapper (Ext'(Flag => False));
end;
