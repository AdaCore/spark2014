package Root_Pkg with Elaborate_Body is
   type Root is abstract tagged null record;
   function Op (X : Root) return Boolean is abstract;
   function Op_Wrapper (Y : Root'Class) return Boolean;
end;
