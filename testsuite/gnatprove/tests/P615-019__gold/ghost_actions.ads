package Ghost_Actions is

   type Status is (Raw, Sanitized, Normalized) with Ghost;
   Current_State : Status with Ghost;

   procedure Sanitize
     with Pre  => Current_State = Raw,
          Post => Current_State = Sanitized;

   procedure Normalize
     with Pre  => Current_State = Sanitized,
          Post => Current_State = Normalized;

   procedure Main_Treatment
     with Pre => Current_State = Normalized;

end Ghost_Actions;
