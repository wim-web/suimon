import Suimon.Theorems.Layout

namespace Suimon

set_option maxHeartbeats 1600000 in
/-- Operational bodies never declare the whole execution successful. The only
    such boundary is the root-frame check performed by idle. --/
theorem transition_succeeded (s next : State) (op : Op)
    (accepted : transition s op = .ok next) (finished : next.status = .succeeded) :
    s.status = .succeeded := by
  have hPlace := place_layoutView
  have hConsume := consume_layoutView
  have hInputs := consumeInputs_layoutView
  have hClose := closeOutputs_layoutView
  have hFresh := freshInstance_layoutView
  have hDecision := decision_layoutView
  have hFrame := closeFrame_layoutView
  have hControl := finishControl_layoutView
  have hStream := streamController_layoutView
  have hOutputs := placeOutputs_layoutView
  have hBody := placeBodyOutputs_layoutView
  have hChannels := consumeChannels_layoutView
  have hStart := startInputs_layoutView
  have hFailure := expireOrFail_layoutView
  have hAdd := addFrame_layoutView
  simp only [State.layoutView, Prod.mk.injEq, State.channelLayout,
    State.frameChannels, State.frameDefinitions] at hPlace hConsume hInputs hClose hFresh hDecision hFrame hControl hStream hOutputs hBody hChannels hStart hFailure hAdd
  cases op <;>
    simp only [transition, require, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, instMonadExceptOfExcept] at accepted
  all_goals
    repeat (first
      | split at accepted
      | (simp only [bind, Except.bind, pure, Except.pure] at accepted)
      | contradiction
      | cases accepted)
  all_goals
    try simp only [putOutput, setInstance, setAttempt] at *
    grind only []

theorem step_succeeded_origin (s next : State) (op : Op)
    (accepted : step s op = .ok next) (finished : next.status = .succeeded) :
    s.status = .succeeded ∨
    (op = .idle ∧ next = idleState s ∧ s.started = true ∧
      ∃ root, s.frame? [] = some root ∧ frameDone s root = true) := by
  rcases step_ok_cases s op next accepted with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · exact .inl (same ▸ finished)
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure, Except.ok.injEq] at executed
      subst next
      by_cases work : s.hasWork = true
      · exact .inl (by simpa [idleState, work] using finished)
      · have status : (if (s.started && (s.frame? []).any (frameDone s)) then
            ExecStatus.succeeded else ExecStatus.blocked) = ExecStatus.succeeded := by
          simpa [idleState, work] using finished
        have success : (s.started && (s.frame? []).any (frameDone s)) = true := by
          split at status
          · assumption
          · contradiction
        simp only [Bool.and_eq_true, Option.any_eq_true] at success
        obtain ⟨started, root, found, done⟩ := success
        exact .inr ⟨rfl, rfl, started, root, found, done⟩
    | _ =>
      simp only [transitionOrIdle] at executed
      exact .inl (transition_succeeded s next _ executed finished)

theorem ConformingSteps.terminal {allows : State → Op → Prop}
    {s next : State} {ops : List Op} (run : ConformingSteps allows s ops next)
    (finished : s.status.terminal = true) : next = s := by
  induction run with
  | nil => rfl
  | cons allowed accepted tail ih =>
    have same := terminal_absorbing _ _ _ finished accepted
    subst_vars
    exact ih finished

/-- A successful finite run has an actual successful root-frame completion;
    its remaining operations are absorbed identities. --/
theorem ConformingSteps.completion {allows : State → Op → Prop}
    {s last : State} {ops : List Op} (run : ConformingSteps allows s ops last)
    (notFinished : s.status ≠ .succeeded) (finished : last.status = .succeeded) :
    ∃ headOps tailOps before root,
      ops = headOps ++ .idle :: tailOps ∧
      ConformingSteps allows s headOps before ∧
      step before .idle = .ok last ∧ last = idleState before ∧
      before.started = true ∧ before.frame? [] = some root ∧ frameDone before root = true := by
  induction run with
  | nil => exact False.elim (notFinished finished)
  | @cons s middle last op ops allowed accepted tail ih =>
    by_cases already : middle.status = .succeeded
    · have terminal : middle.status.terminal = true := by rw [already]; rfl
      have same := tail.terminal terminal
      subst last
      rcases step_succeeded_origin s middle op accepted already with earlier | ⟨idle, result, started, root, found, done⟩
      · exact False.elim (notFinished earlier)
      · subst op
        exact ⟨[], ops, s, root, rfl, .nil s, accepted, result, started, found, done⟩
    · obtain ⟨headOps, tailOps, before, root, schedule, head, complete, result, started, found, done⟩ :=
        ih already finished
      exact ⟨op :: headOps, tailOps, before, root, by simp [schedule],
        .cons allowed accepted head, complete, result, started, found, done⟩

end Suimon
