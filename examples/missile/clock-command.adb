with Test_Keywords,Ada.Text_Io;
with Test, Test.Checking;
separate(Clock)
procedure Command is
   type Clock_Keyword is (Reset,Increment,Check);
   package Clock_Io is new Ada.Text_Io.Enumeration_Io(Clock_Keyword);

   package Millisecond_Io is new Ada.Text_Io.Integer_Io(Millisecond);

   type Clock_Check_Kw is (Valid, Time);
   package Clock_Check_Io is new Ada.Text_Io.Enumeration_Io(Clock_Check_Kw);

   Action : Clock_Keyword;
   M : Millisecond;

   Unit_Name : constant String := "Clock";

   procedure Check is
      This_Check : Clock_Check_Kw;
      Exp_Bool,Act_Bool : Boolean;
      Exp_Time, Act_Time : Millisecond;
   begin
      Read(T => Act_Time,
           Valid => Act_Bool);
      Clock_Check_Io.Get(This_Check);
      Ada.Text_Io.Put_Line(Clock_Check_Kw'Image(This_Check));

      case This_Check is
         when Valid =>
            Test_Keywords.Bool_Io.Get(Exp_Bool);
            Test.Checking.Bool(S => Unit_Name & " " & Clock_Check_Kw'Image(This_Check),
                               Expected => Exp_Bool,
                               Actual   => Act_Bool);
         when Time =>
            Millisecond_Io.Get(Exp_Time);
            Test.Align(Unit_Name & " " & Clock_Check_Kw'Image(This_Check));
            if Exp_Time = Act_Time then
               Test.Pass(" ");
            else
               Test.Fail("E=" & Millisecond'Image(Exp_Time) &
                           "ms, A=" & Millisecond'Image(Act_Time) &
                           "ms");
            end if;
      end case;
   end Check;
begin
   Clock_Io.Get(Action);
   case Action is
      when Reset =>
         Ada.Text_Io.Put_Line("Clock reset");
         Reset;
      when Increment =>
         Test_Keywords.Millisec_Io.Get(M);
         Ada.Text_Io.Put_Line("Clock increment " & Millisecond'Image(M)
                              & "ms");
         Cycle(Plus => M);
      when Check =>
         Ada.Text_Io.Put("Clock Check ");
         Check;
   end case;
   Ada.Text_Io.skip_Line;
exception
   when others =>
      Ada.Text_Io.Put_Line("Exception in Clock Command");
end Command;
