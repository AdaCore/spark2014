package Private_Record with SPARK_Mode is
   type Result_Ty (Found : Boolean) is private;

   function Get_Content (R : Result_Ty) return Positive with
     Pre => R.Found = True;

   function Mk_Result (Found : Boolean; Content : Positive := 1) return Result_Ty with
     Post => Mk_Result'Result.Found = Found
     and then (if Found then Get_Content (Mk_Result'Result) = Content);
   pragma Annotate (GNATprove, Terminating, Mk_Result);

private
   pragma SPARK_Mode (Off);

   type Result_Ty (Found : Boolean) is record
      case Found is
         when True =>
            Content : Positive;
         when False => null;
      end case;
   end record;

   function Get_Content (R : Result_Ty) return Positive is (R.Content);

   function Mk_Result (Found : Boolean; Content : Positive := 1) return Result_Ty is
     (if Found then (Found => True, Content => Content)
      else (Found => False));

end;
