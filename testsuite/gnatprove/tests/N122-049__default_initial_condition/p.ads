package P
  with SPARK_Mode => On
is
   --  N122-049 - Test cases for Default_Initial_Condition aspect.

   --  Proposal from Steve B specifies 3 ways that
   --  Default_Initial_Condition can be used.  There
   --  is also the possibility of not having it at all,
   --  so that's FOUR possibilities.
   --  These cases are denoted below as
   --   visible:[none|default|null|predicate]
   --
   --  The completion of a private types can deliver three
   --  possibilities - no, partial, and full initialization.
   --  These cases are denoted below as
   --   completion:[none|partial|full]
   --
   --  There are threfore 12 cases to consider.

   --  Case 1 - visible:none, completion: none
   type T1 is private;

   --  Case 2 - visible:none, completion: partial
   type T2 is private;

   --  Case 3 - visible:none, completion: full
   type T3 is private;


   --  Case 4 - visible:default, completion: none
   type T4 is private
     with Default_Initial_Condition;

   --  Case 5 - visible:default, completion: partial
   type T5 is private
     with Default_Initial_Condition;

   --  Case 6 - visible:default, completion: full
   type T6 is private
     with Default_Initial_Condition;


   --  Case 7 - visible:null, completion: none
   type T7 is private
     with Default_Initial_Condition => null;

   --  Case 8 - visible:null, completion: partial
   type T8 is private
     with Default_Initial_Condition => null;

   --  Case 9 - visible:null, completion: full
   type T9 is private
     with Default_Initial_Condition => null;

   --  Case 10 - visible:predicate, completion: none
   type T10 is private
     with Default_Initial_Condition => P10 (T10);
   function P10 (X : in T10) return Boolean with
     Global   => null,
     Annotate => (GNATprove, Always_Return);

   --  Case 11 - visible:predicate, completion: partial
   type T11 is private
     with Default_Initial_Condition => P11 (T11);
   function P11 (X : in T11) return Boolean with
     Global   => null,
     Annotate => (GNATprove, Always_Return);

   --  Case 12 - visible:predicate, completion: full
   type T12 is private
     with Default_Initial_Condition => P12 (T12);
   function P12 (X : in T12) return Boolean with
     Global   => null,
     Annotate => (GNATprove, Always_Return);



private
   --  Case 1 - visible:none, completion: none
   --  Required behaviour:
   --    Legality:  OK. no error, no warning
   --    Flow:      clients see objects as uninitialized at declaration
   --    Proof:     as Flow
   --    Comment:   Basic case as per existing SPARK rules
   type T1 is record
      F1, F2 : Integer;
   end record;

   --  Case 2 - visible:none, completion: partial
   --    Legality:  Error as per RM 3.8(1), but see case 5 below
   --    Flow:      NA
   --    Proof:     NA
   type T2 is record
      F1 : Integer := 0;
      F2 : Integer;
   end record;

   --  Case 3 - visible:none, completion: full
   --    Legality:  OK
   --    Flow:      clients see objects as uninitialized at declaration
   --    Proof:     as Flow
   --    Comment:   Interesting - should the tool be allowed to "peek" inside the
   --               private part here and conclude that T3 really is FDI?  RCC does
   --               not think so.  No Peeking!
   type T3 is record
      F1 : Integer := 0;
      F2 : Integer := 0;
   end record;

   --  Case 4 - visible:default, completion: none
   --    Legality:  Error
   --    Flow:      NA
   --    Proof:     NA
   --    Comment:   Surely an error?  Visible makes a firm promise,
   --               completion fails to deliver. Anything else would result
   --               in unsoundness in flow analysis.
   type T4 is record
      F1 : Integer;
      F2 : Integer;
   end record;

   --  Case 5 - visible:default, completion: partial
   --    Legality:  Suppressible warning
   --    Flow:      clients see objects as initialized at declaration
   --    Proof:     as Flow
   --    Comment:   A common use-case and pattern, so needs to be a suppressible
   --               warning here in the completion.  Clients get no error or warning
   --               in their code.  Needed for the "data structure so large I don't
   --               want to have to initialize all of it, but I want the client
   --               to think it is" pattern.  Possible rule change needed in RM 3.8(1) ???
   type T5 is record
      F1 : Integer := 0;
      F2 : Integer;
   end record;

   --  Case 6 - visible:default, completion: full
   --    Legality:  OK
   --    Flow:      clients see objects as initialized at declaration
   --    Proof:     as Flow
   --    Comment:   Must be OK, right? Completion delivers promise made by visible.
   type T6 is record
      F1 : Integer := 0;
      F2 : Integer := 0;
   end record;


   --  Case 7 - visible:null, completion: none
   --    Legality: OK
   --    Flow:     clients see objects as uninitialized at declaration
   --    Proof:    as Flow
   --    Comment:  As case 1, but the writer has been more explicit
   type T7 is record
      F1 : Integer;
      F2 : Integer;
   end record;

   --  Case 8 - visible:null, completion: partial
   --    Legality:  Error as per RM 3.8(1), but see case 5 above
   --    Flow:      NA
   --    Proof:     NA
   --    Comment:   As case 2, but more explicit
   type T8 is record
      F1 : Integer;
      F2 : Integer := 0;
   end record;

   --  Case 9 - visible:null, completion: full
   --    Legality:  OK
   --    Flow:      clients see objects as uninitialized at declaration
   --    Proof:     as Flow
   --    Comment:   As case 3
   type T9 is record
      F1 : Integer := 0;
      F2 : Integer := 0;
   end record;


   --  Case 10 - visible:predicate, completion: none
   --    Legality:  Error
   --    Flow:      NA
   --    Proof:     NA
   --    Comment:   As per case 4.  Visible promises init, but
   --               fails to deliver.
   type T10 is record
      F1 : Integer;
      F2 : Integer;
   end record;

   --  Case 11 - visible:predicate, completion: partial
   --    Legality:  Suppressible warning
   --    Flow:      clients see objects as initialized at declaration
   --    Proof:     as Flow, AND P11(T11) assumed true following declaration
   --    Comment:   As per case 5 - needed for containers, large data structure and so on.
   type T11 is record
      F1 : Integer := 0;
      F2 : Integer;
   end record;

   --  Case 12 - visible:predicate, completion: full
   --    Legality:  OK
   --    Flow:      clients see objects as initialized at declaration
   --    Proof:     as Flow, AND P12(T12) assumed true following declaration
   --    Comment:   As per case 6, but adding the predicate
   type T12 is record
      F1 : Integer := 0;
      F2 : Integer := 0;
   end record;

end P;
