with String_Search; use String_Search;

procedure Test_Search is
   All_Men : constant Text :=
     "We hold these truths to be self-evident, that all men are created equal,"
     & " that they are endowed by their Creator with certain unalienable "
     & "Rights, that among these are Life, Liberty and the Pursuit of "
     & "Happiness. That to secure these rights, Governments are instituted "
     & "among Men, deriving their just powers from the consent of the governed";
begin
   pragma Assert (Brute_Force ("just powers", All_Men) > 0);
   pragma Assert (Brute_Force_Slice ("just powers", All_Men) > 0);
   pragma Assert (QS ("just powers", All_Men) > 0);

   pragma Assert (Brute_Force ("austin powers", All_Men) = 0);
   pragma Assert (Brute_Force_Slice ("austin powers", All_Men) = 0);
   pragma Assert (QS ("austin powers", All_Men) = 0);
end Test_Search;
