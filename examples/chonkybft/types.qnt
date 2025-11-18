// -*- mode: Bluespec; -*-

module types {
    import option.* from "./spells/option"

    // For specification purposes, a block is just an indivisible string.
    type Block = str

    // For specification purposes, we represent a hash as the string itself
    type BlockHash = str

    // Get the "hash" of a string
    pure def hash(b: str): BlockHash = b

    // View number
    type ViewNumber = int

    // Block number
    type BlockNumber = int

    // Weight
    type Weight = int

    // A replica id is a unique replica identifier
    type ReplicaId = str

    // Each replica id has a private/public key pair assigned to it
    type ReplicaKey = str

    // Similar to ReplicaId, we model the signature as the replica name
    type Signature = str

    // For specification purposes, an aggregate signature is simply a set of signatures
    type AggregateSignature = Set[Signature]

    /// A block with a matching valid certificate
    type CommittedBlock = {
        block: Block,
        commit_qc: CommitQC,
    }

    type Phase = PhasePrepare | PhaseCommit | PhaseTimeout

    type CommitVote = {
        // The current view
        view: ViewNumber,
        // The number of the block that the replica is committing to
        block_number: BlockNumber,
        // The hash of the block that the replica is committing to
        block_hash: BlockHash,
    }

    type SignedCommitVote = {
        // The commit
        vote: CommitVote,
        // Signature of the sender
        sig: Signature,
    }

    pure val COMMIT_VOTE_NONE: Option[CommitVote] = None

    // If we have QUORUM_WEIGHT identical commit votes from different replicas
    type CommitQC = {
        // The commit
        vote: CommitVote,
        // The aggregate signature of the replicas
        agg_sig: AggregateSignature,
    }

    pure val HIGH_COMMIT_QC_NONE: Option[CommitQC] = None

    // Timeout votes are sent from replicas to replicas
    type TimeoutVote = {
        // The current view
        view: ViewNumber,
        // The commit vote with the highest view that this replica has signed
        high_vote: Option[CommitVote],
        // The view number of the highest commit QC that this replica has observed
        high_commit_qc_view: Option[ViewNumber],
    }

    pure val VIEW_NUMBER_NONE: Option[ViewNumber] = None

    type SignedTimeoutVote = {
        // The timeout
        vote: TimeoutVote,
        // Signature of the sender
        sig: Signature,
        // The commit QC with the highest view that this replica has observed
        high_commit_qc: Option[CommitQC],
    }

    // Timeout QC aggregates different messages
    type TimeoutQC = {
        // A collection of the replica timeout votes
        votes: ReplicaKey -> TimeoutVote,
        // The aggregate signature of the replicas
        agg_sig: AggregateSignature,
        // The commit QC with the highest view
        high_commit_qc: Option[CommitQC],
        // current view computed from the votes
        ghost_view: ViewNumber,
    }

    pure val HIGH_TIMEOUT_QC_NONE: Option[TimeoutQC] = None

    type Justification =
            // Proposal after finalizing a block
            Commit(CommitQC)
            // Proposal after a view timeout
        |   Timeout(TimeoutQC)

    type Proposal = {
        // Block that the leader is proposing, if this is a new proposal
        block: Option[Block],
        // What attests to the validity of this proposal
        justification: Justification,
        // Signature of the sender
        sig: Signature,
        // The block number of the proposed block
        ghost_block_number: BlockNumber,
    }

    // New view messages are sent from replicas to replicas for synchronization
    type NewView = {
        // What attests to the validity of this view change
        justification: Justification,
        // Signature of the sender
        sig: Signature,
    }

    type StepKind =
          InitStep | ProposerStep(ReplicaId) | OnProposalStep(ReplicaId) | OnCommitStep(ReplicaId)
        | OnTimeoutStep(ReplicaId) | OnTimerIsFinishedStep(ReplicaId)
        | OnNewViewStep({ id: ReplicaId, view: ViewNumber }) | FaultyStep | FetchStep(ReplicaId) | AnyStep
}
