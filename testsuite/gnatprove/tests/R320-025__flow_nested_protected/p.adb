package body P is

   protected body Outer_Type is
      function Outer_Fun return Integer is
         protected type Inner_Type is
            function Inner_Fun return Integer;
         private
            Inner_Data : Integer := 0;
         end;
         --  An object of this type, when created, would violate the
         --  No_Local_Protected_Objects restriction of the Ravenscar profile;
         --  but the type declaration itself is not a violation. (For example,
         --  we could even reference its 'Size attribute.)

         protected body Inner_Type is
            function Inner_Fun return Integer is
               type T is new Integer range Inner_Data .. Outer_Data;
               --  Protected components referenced in range bounds belong to
               --  current instances of protected types that act as an implicit
               --  formal parameter of mode IN (Inner_Type) and a global of
               --  mode In (Outer_Type); such references are not considered as
               --  "variable inputs", so the type definition is legal wrt to
               --  SPARK rules.
            begin
               return 0;
            end;
         end;
      begin
         return 0;
      end;
   end;
end;
