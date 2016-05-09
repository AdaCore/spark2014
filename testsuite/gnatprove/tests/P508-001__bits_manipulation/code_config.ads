package Code_Config is

   pragma Pure;

   type Optimizations is (Slow_And_Small, Normal, Fast_And_Large);
   -- Select algorithms in code: for instance, function "Sort" may
   -- use bubble-sort or quick-sort, depending on optimization value

   type Inlining is (Default, Inline, Inline_Always);
   -- Default - no explicitly defined inlining,
   --           compiler will select strategy based
   --           on command-line flags
   --
   -- Inline - set 'with Inline' on functions
   --          to force compiler to inline them
   --
   -- Inline_Always - all functions will get
   --                 'with Inline_Always' aspect
   --                 and will be inlined even if
   --                 -fno-inline command-line flag
   --                 is set

   type Safety is (Default, Unsafe, Safe, Extra_Safe);
   -- Default - no explicitly set safety
   --           attributes and pragmas in code
   --
   -- Unsafe - code will switch off all checks via
   --          corresponding pragmas
   --
   -- Safe - code will turn on all pragmas
   --        for run - time checks
   --
   -- Extra-Safe - same as Safe plus some explicit
   --              checks by code itself

   generic
      Proved : Boolean := True;
      -- If True then only formally proved
      -- functions will be used

      Optimize_For : Optimizations := Normal;
      -- Select optimizations, if code supports them

      Inline : Inlining := Default;
      -- Inlining - user may choose strategy for
      --            code inlining

      Safe : Safety := Default;
      -- If supported then some extra checks and
      -- so on may be used by code

   package Parameters is end Parameters;

end Code_Config;
