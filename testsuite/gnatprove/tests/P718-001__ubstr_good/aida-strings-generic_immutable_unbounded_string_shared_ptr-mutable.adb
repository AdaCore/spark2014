with Aida.Strings.Generic_Immutable_Unbounded_String.Mutable;

package body Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr.Mutable with SPARK_Mode => Off is

   package MUS is new US.Mutable;

   procedure Initialize (This : in out Mutable_T;
                         Text : String)
   is
--      V : constant US_Ptr := new US.T;
   begin
--      This.SP := Smart_Pointers.Create (V);
      MUS.Initialize (This => MUS.Mutable_T (Smart_Pointers.Value (This.SP).all),
                      Text => Text);
   end Initialize;

   procedure Append (This : in out Mutable_T;
                     Text : String) is
   begin
      MUS.Append (This => MUS.Mutable_T (Smart_Pointers.Value (This.SP).all),
                  Text => Text);
   end Append;

end Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr.Mutable;
