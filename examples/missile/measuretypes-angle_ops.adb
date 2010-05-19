package body MeasureTypes.Angle_ops
is
   -- Simple type renamings for brevity
   subtype Millirad is Measuretypes.Millirad;
   subtype Canon_Millirad is Measuretypes.Canon_Millirad;
   -- Canonical millirads are 0deg .. 359.999deg

   -- Canonicalise an angle into -180..+179 degree range
   function Canon(Orig_Angle : Millirad) return Canon_Millirad
   is
      Answer : Millirad;
   begin
      Answer := Orig_Angle;
      if Answer > Canon_Millirad'Last then
         Answer := Canon_Millirad'First + (Answer - Canon_Millirad'Last);
      elsif Answer < Canon_Millirad'First then
         Answer := Canon_Millirad'Last - (Canon_Millirad'First - Answer);
      else
         -- Nothing to do
         null;
      end if;
      -- Useful for debugging
      --Ada.Text_Io.Put_Line("Canon map of " &
      --                    Millirad'Image(Orig_Angle) &
      --                     "mR is " &
      --                     Millirad'Image(Answer) & "mR");
      return Answer;
   end Canon;

   function Mul(Orig_Angle : Measuretypes.Millirad;
                Mult       : Integer)
               return Measuretypes.Millirad
   is
      Ans : Measuretypes.Millirad;
   begin
      Ans := Orig_Angle * Measuretypes.Millirad(Mult);
      return Canon(Ans);
   end Mul;

   -- Add two angles, preventing overflow
   function Sum(Left, Right : Measuretypes.Millirad)
               return Measuretypes.Millirad
   is
      Answer : Millirad;
      Lc, Rc : Canon_Millirad;
   begin
      Lc := Canon(Left);
      Rc := Canon(Right);
      if Lc >= 0 then
         if Rc >= 0 then
            -- Two +ve angles; get the sum minus 180 degrees
            Answer := (Lc - Measuretypes.Angle_Half) + Rc;
            if Answer > 0 then
               -- Adding 180 degrees makes it go negative
               Answer := Answer + Measuretypes.Angle_Minushalf;
            else
               -- Adding 180 degrees makes it go positive
               Answer := Lc + Rc;
            end if;
         else
            -- Right -ve, left +ve so we're OK
            Answer := Lc + Rc;
         end if;
      else
         if Rc >= 0 then
            -- Left -ve, right +ve
            Answer := Lc + Rc;
         else
            -- Two -ve angles; get the sum plus 180 degrees
            Answer := (Lc + Measuretypes.Angle_Half) + Rc;
            if Answer >= 0 then
               -- Subtracting 180 degrees keeps it negative
               Answer := Lc + Rc;
            else
               -- Subtracting 180 degrees makes it positive
               Answer := Measuretypes.Angle_Half + Answer;
            end if;
         end if;
      end if;
      return Answer;
   end Sum;

   -- Reflect an angle about N-S
   function Negate(Orig_Angle : Measuretypes.Millirad)
                  return Measuretypes.Millirad
   is
   begin
      return -Orig_Angle;
   end Negate;

   function Diff(Left, Right : Measuretypes.Millirad)
                return Measuretypes.Millirad
   is
      Rminus, Answer : Millirad;
   begin
      Rminus := Negate(Right);
      Answer := Sum(Left => Left,Right => Rminus);
      return Answer;
   end Diff;

   function Create_Angle(Word : Systemtypes.Word)
                        return Measuretypes.Millirad
   is
      Sign_word : Systemtypes.Integer32;
      Answer : Millirad;
   begin
      if Word >= 2**15 then
         Sign_Word := -Systemtypes.integer32(Word - Systemtypes.Word(2**15));
      else
         Sign_Word := Systemtypes.Integer32(Word);
      end if;
      if Sign_Word > Systemtypes.Integer32(Millirad'Last) then
         Answer := Millirad'Last;
      elsif Sign_Word < Systemtypes.Integer32(Millirad'First) then
         Answer := Millirad'First;
      else
         Answer := Millirad(Sign_Word);
      end if;
      return Answer;
   end Create_angle;

   function Millirad_To_word(Orig_angle : Measuretypes.Millirad)
                            return Systemtypes.Word
   is
      Sign_word : Systemtypes.Integer32;
      Word : Systemtypes.Word;
      Neg_Sign : Boolean := False;
   begin
      Sign_Word := Systemtypes.Integer32(Canon(Orig_Angle));
      if Sign_Word < 0 then
         Sign_Word := -Sign_Word;
         Neg_Sign := True;
      end if;
      Word := Systemtypes.Word(Sign_Word);
      if Neg_Sign then
         Word := Word + 2**15;
      end if;
      return word;
   end Millirad_To_word;

   function Int_To_Millirad(Count : in Systemtypes.Integer32)
                            return Measuretypes.Millirad
   is
      Neg_Sign : Boolean;
      Tmp_Count : Systemtypes.Unsigned32;
      Answer : Millirad;
   begin
      if Count < 0 then
         Neg_Sign := True;
         Tmp_Count := Systemtypes.Unsigned32(-Count);
      else
         Neg_Sign := False;
         Tmp_Count := Systemtypes.Unsigned32(Count);
      end if;
      -- This may represent more than one revolution around the circle,
      -- so divide by a full circle circumference and take the remainder
      Tmp_Count := Tmp_Count mod Systemtypes.Unsigned32(Measuretypes.Angle_Full);
      -- Restore sign
      if Neg_Sign then
         Answer := -Millirad(Tmp_Count);
      else
         Answer := Millirad(Tmp_Count);
      end if;
      return Answer;
   end Int_To_Millirad;

   function Degree_To_Millirad(Orig_Degree : Measuretypes.Angle_Degrees)
                              return Measuretypes.Millirad
   is
      Count : Systemtypes.Integer32;
   begin
      -- Scale angle_full by orig_degree/(degrees in a full circle)
      Count := Systemtypes.Integer32(Measuretypes.Angle_Full) *
        Systemtypes.Integer32(Orig_Degree);
      Count := Count / Systemtypes.Integer32(Measuretypes.Angle_Degrees'Last+1);
      -- And convert this number in the (-7000,+7000) range into a millirad
      return Int_To_Millirad(Count);
   end Degree_To_Millirad;

   -- Map millirads back into a round number of degrees (0..359)
   function Round_Degree(Orig_Angle : Measuretypes.Millirad)
                        return Measuretypes.Angle_Degrees
   is
      Tmp_mr : Millirad;
      Tmp_Int : SystemTypes.Integer32;
      Tmp : Measuretypes.Angle_Degrees;
   begin
      Tmp_mr := Canon(Orig_Angle); -- force into Angle_Minushalf..Angle_Half
      if Tmp_Mr < 0 then
         -- Force into 0..Angle_Full
         Tmp_Mr := Measuretypes.Angle_Full + Tmp_Mr;
      end if;
      Tmp_Int := (SystemTypes.Integer32(Tmp_Mr) * 360) /
        Systemtypes.Integer32(Measuretypes.Angle_Full);
      if Tmp_Int >= 360 then
         Tmp := 0;
      else
         Tmp := Measuretypes.Angle_Degrees(Tmp_Int);
      end if;
      -- Useful for debugging
      --Ada.Text_IO.Put_Line("Rounded " &
      --                     Measuretypes.Millirad'Image(Orig_Angle) &
      --                     "mR to " &
      --                     Measuretypes.Angle_Degrees'Image(Tmp) &
      --                     "deg");
      return tmp;
   end Round_Degree;

end Measuretypes.Angle_ops;
