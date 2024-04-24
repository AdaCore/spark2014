with Ada.Strings.Unbounded;
with Sinfo.Nodes; use Sinfo.Nodes;
with SPARK_Util; use SPARK_Util;

package body Errout_Wrapper is

   ------------
   -- Create --
   ------------

   function Create
     (Msg           : String;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message is
   begin
      return Message'(Msg'Length, Names, Secondary_Loc, Explain_Code, Msg);
   end Create;

   function Create_N
     (Msg           : String;
      N             : Node_Id := Empty;
      Names         : Name_Id_Lists.List := Name_Id_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message
   is
      use Ada.Strings.Unbounded;
      Buf : Unbounded_String;
      Index : Integer := Msg'First;
      C : Name_Id_Lists.Cursor := Names.First;
   begin
      --  Given that message objects hold lists of nodes, we need to do the
      --  replacement ourselves.
      while Index in Msg'Range loop
         if Msg (Index) = ''' then
            Append (Buf, Msg (Index));
            Index := Index + 1;
            Append (Buf, Msg (Index));
         elsif Msg (Index) = '&' then
            Append (Buf, To_String (Name_Id_Lists.Element (C), Sloc (N)));
            Name_Id_Lists.Next (C);
         else
            Append (Buf, Msg (Index));
         end if;
         Index := Index + 1;
      end loop;
      return
        Message'(Length (Buf),
                 Node_Lists.Empty,
                 Secondary_Loc,
                 Explain_Code,
                 To_String (Buf));
   end Create_N;

   -----------------
   -- Error_Msg_N --
   -----------------

   procedure Error_Msg_N
     (Msg           : Message;
      N             : Node_Id;
      Kind          : Msg_Kind := MK_Error;
      First         : Boolean := False;
      Continuations : Message_Lists.List := Message_Lists.Empty)
   is
      procedure Print_Msg (Msg : Message; Cont : Boolean);

      function First_Explain_Code return Explain_Code_Kind;
      --  Return the first explain code found in the message or continuations
      --  (in that order).

      ------------------------
      -- First_Explain_Code --
      ------------------------

      function First_Explain_Code return Explain_Code_Kind is
      begin
         if Msg.Explain_Code /= EC_None then
            return Msg.Explain_Code;
         end if;
         for Cont of Continuations loop
            if Cont.Explain_Code /= EC_None then
               return Cont.Explain_Code;
            end if;
         end loop;
         return EC_None;
      end First_Explain_Code;

      ---------------
      -- Print_Msg --
      ---------------

      procedure Print_Msg (Msg : Message; Cont : Boolean) is
         Prefix : constant String :=
           (case Kind is
               when MK_Error => "",
               when MK_Warning => "?",
               when MK_Info => "info: ?");
         Cont_Prefix : constant String :=
           (case Kind is
               when MK_Error => "\",
               when MK_Warning | MK_Info => "\?");
         use Node_Lists;
         Expl_Code : constant String :=
           (if Msg.Explain_Code = EC_None then ""
            else " '[" & To_String (Msg.Explain_Code) & "']");
         Names : constant Node_Lists.List :=
           (if not Msg.Names.Is_Empty then Node_Lists.List'(Msg.Names)
            else Node_Lists.List'([N]));
         C : Cursor := Next (Names.First);
      begin
         Errout.Error_Msg_Sloc := Msg.Secondary_Loc;
         if Has_Element (C) then
            Errout.Error_Msg_Node_2 := Element (C);
            Next (C);
            if Has_Element (C) then
               Errout.Error_Msg_Node_3 := Element (C);
               Next (C);
               if Has_Element (C) then
                  Errout.Error_Msg_Node_4 := Element (C);
                  Next (C);
               end if;
               --  ??? ideally would need to go up to 6
            end if;

         end if;
         declare
            S : constant String :=
              (if Cont then Cont_Prefix else Prefix) & Msg.Msg & Expl_Code;
         begin
            if First then
               Errout.Error_Msg_FE (S, N, Element (Names.First));
            else
               Errout.Error_Msg_NE (S, N, Element (Names.First));
            end if;
         end;
      end Print_Msg;

   begin
      Print_Msg (Msg, Cont => False);
      for Cont of Continuations loop
         Print_Msg (Cont, Cont => True);
      end loop;
      declare
         Code : constant Explain_Code_Kind := First_Explain_Code;
      begin
         if Code /= EC_None then
            Print_Msg (Create
                       ("launch ""gnatprove --explain="
                        & To_String (Code)
                        & """ for more information"),
                       Cont => True);
         end if;
      end;
   end Error_Msg_N;

   -----------------
   -- Error_Msg_N --
   -----------------

   procedure Error_Msg_N
     (Msg           : String;
      N             : Node_Id;
      Kind          : Msg_Kind := MK_Error;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None;
      First         : Boolean := False;
      Continuations : String_Lists.List := String_Lists.Empty)
   is
      Conts : Message_Lists.List := Message_Lists.Empty;
   begin
      for S of Continuations loop
         Conts.Append (Create (S));
      end loop;
      Error_Msg_N (Create (Msg, Names, Secondary_Loc, Explain_Code),
                   N,
                   Kind,
                   First => First,
                   Continuations => Conts);
   end Error_Msg_N;

end Errout_Wrapper;
