using ExprRules
using DataStructures
using Statistics: mean
using ProgressMeter
import Base.length
using Printf
using BSON: @save, @load
using JSON

const Gamma = RuleNode
const channelsize = Inf

struct Tails
    tails::Vector{Gamma}
    logp::Float64
end

struct Head
    head::Gamma
    logp::Float64
end

struct Direction
    logp::Float64
    ind::Int
    z::Int

    Direction(; logp=logp, ind=ind, z=z) = new(logp, ind, z)
end

struct GhostStat
    ghost::Gamma
    count::Int
end

mutable struct GrammarInfo
    hiddentails::Dict{Int, Gamma}
    axiomlength::Int
    length::Int
    holesinds::Vector{Int}
end

ishole(GI::GrammarInfo, d::Gamma) = d.ind ∈ GI.holesinds

import Base.isless
isless(g1::GhostStat, g2::GhostStat) = g1.count < g2.count

ishole(G::Grammar, ind::Int) = G.rules[ind] isa Symbol
ishole(G::Grammar, d::Gamma) = G.rules[d.ind] isa Symbol
length(G::Grammar) = length(G.rules)
softmax(xs) = exp.(xs) / sum(exp.(xs))

import Base.show
show(io::IO, ::MIME"text/plain", d::Direction) = show(io, "$(d.ind) #$(d.logp) {$(d.z)})")

function countshards(X::Vector{T}, maxlength=length(X)) where T
    shards = DefaultDict{Vector{T}, Int}(0)

    for ℓ = 1:maxlength, start = 1:length(X) - ℓ + 1
        substring = X[start:start+ℓ-1]
        shards[substring] += 1
    end

    shards
end

import Base.getindex
function getindex(xs::Cons{T}, ind::Int64) where T
    ind > length(xs) && error("index overflow")

    for _ = 1:ind-1
        xs = tail(xs)
    end

    first(xs)
end

function getindex(xs::Cons{T}, range::UnitRange{Int}) where T
    collect(xs[ind] for ind in range)
end

# fallback
import Base.occursin
function occursin(x::AbstractVector, xs::AbstractVector)
    if isempty(x) || isempty(xs)
        return false
    end

    xind = 1
    xsind = 1
    xssave = 0

    while xsind <= length(xs)
        if x[xind] == xs[xsind]
            xind == length(x) && return true

            if xssave == 0
                xssave = xsind
            end
            xind += 1

        elseif xind > 1
            xind = 1
            xsind = xssave
            xssave = 0
        end

        xsind += 1
    end

    return false
end

function forcetrees(X::T, Z) where T
    ℓ = maximum(length.(keys(Z)))

    ind = 1
    l = ℓ

    trees = Gamma[]
    outtrees = Vector{T}()
    while ind <= length(X)
        eind = min(length(X), ind+l)
        x = X[ind:eind]

        if haskey(Z, x)
            push!(trees, Z[x])
            push!(outtrees, x)

            ind += l + 1
            l = ℓ
        else
            l -= 1
        end
    end

    outtrees, trees
end

function flatvase(X, Z, W)
    Backward = Dict{Int, Vector{String}}(ind => [] for ind = 1:length(X))
    Coding = Dict{String, Gamma}()

    for (z, γ) in Z
        z = join(z, "")
        Coding[z] = γ

        for range in findall(z, X)
            push!(Backward[range[end]], z)
        end
    end

    O = Inf * ones(length(X) + 1)
    O[1] = 0
    S = ["" for _ = 1:length(X)]

    for ind in 1:length(X)
        mino = Inf

        for z in Backward[ind]
            if mino > W[z] + O[ind - length(z) + 1]
                mino = W[z] + O[ind - length(z) + 1]
                S[ind] = z
            end
        end

        O[ind + 1] = mino
    end

    ind = length(X)
    out = []
    trees = []
    while ind > 0
        push!(out, S[ind])
        push!(trees, Coding[S[ind]])
        ind -= length(S[ind])
    end

    @assert join(reverse(out), "") == X

    trees
end

function get_childtypes(rule::Any, types::AbstractVector{Symbol})
    retval = Symbol[]
    if isa(rule, Expr)
        for arg in rule.args
            append!(retval, get_childtypes(arg, types))
        end
    elseif rule ∈ types
        push!(retval, rule)
    end
    return retval
end

function fancy(G, d)
    if ishole(G, d)
        return string(d)
    end

    if isterminal(G, d.ind)
        return eval(get_executable(d, G))
    end

    tails = join(map(t -> fancy(G, t), d.children), " ")

    return "(f$(d.ind) $(tails))"
end

function addhole!(G::Grammar, type::Symbol)
    idx = length(G.rules) + 1

    push!(G.rules, type)
    push!(G.types, type)
    push!(G.isterminal, true)
    push!(G.iseval, false)
    push!(G.bytype[type], idx)
    push!(G.childtypes, [])
end

function isequal0(G::Grammar, d1::Gamma, d2::Gamma)
    if ishole(G, d1) || ishole(G, d2)
        return true
    end

    if d1.ind != d2.ind || length(d1.children) != length(d2.children)
        return false
    end

    for ind in 1:length(d1.children)
        if !isequal0(G, d1.children[ind], d2.children[ind])
            return false
        end
    end

    return true
end

function findhole(G::Grammar, type::Symbol)
    for (ind, (orule, otype)) in enumerate(zip(G.rules, G.types))
        if orule isa Symbol && orule == type
            return ind
        end
    end

    throw(error("there's no hole with type $type in \n$G"))
end

function marktree(G::Grammar, tree::Gamma)
    qq = Queue{RuleNode}()
    enqueue!(qq, tree)

    # per z, or per node
    paths = []
    z = 1

    for n in qq
        if isempty(n.children)
            push!(paths, [])
        else
            sources = []

            for tail in n.children
                z += 1

                holeind = findhole(G, return_type(G, tail))

                directions = [
                    Direction(logp=0.0, ind=tail.ind, z=z), # one for a real tail
                    Direction(logp=0.0, ind=holeind, z=-1)  # one for it's impostor
                ]

                push!(sources, directions)
                enqueue!(qq, tail)
            end

            push!(paths, sources)
        end
    end

    paths
end

function makepaths(G::Grammar, Q::Vector{Float64}, forbidden, withholes=false)
    perrule =  Vector{Vector{Vector{Direction}}}()

    for pind in 1:length(G.rules)
        if isterminal(G, pind)
            push!(perrule, Direction[])
            continue
        end

        pertail = Vector{Vector{Direction}}()

        for (argind, tailtype) in enumerate(child_types(G, pind))
            perarg = Direction[]

            for tind in G.bytype[tailtype]
                !withholes && ishole(G, tind) && continue

                disallowed = false
                if haskey(forbidden, pind)
                    for (testargind, forbid) in forbidden[pind]
                        if testargind(argind) && tind == forbid
                            disallowed = true
                            break
                        end
                    end
                end
                disallowed && continue

                push!(perarg, Direction(ind=tind, logp=Q[tind], z=-1))
            end

            push!(pertail, perarg)
        end

        push!(perrule, pertail)
    end

    perrule
end

function groom(ch, G, sources, alogp, budget, paths)
    if isempty(sources)
        push!(ch, Tails(Gamma[], alogp))
        return
    end

    directions = sources[1]
    nextsources = sources[2:end]

    for dir in directions
        budget + dir.logp < 0 && continue

        # expand in this direction
        for tree in Channel{Head}(channelsize) do nch
            penumerate(nch, G, Gamma(dir.ind), dir.logp, budget + dir.logp, paths, z=dir.z)
        end
            # expand in all other directions
            for tails in Channel{Tails}(channelsize) do nnch
                groom(nnch, G, nextsources, alogp + tree.logp, budget + tree.logp, paths)
            end
                push!(ch, Tails(Gamma[tree.head; tails.tails], tails.logp))
            end
        end
    end
end


function penumerate(ch::Channel, G::Grammar, n::Gamma, nlogp::Float64, budget::Float64, paths; z=-1)
    if budget < 0 || isterminal(G, n)
        push!(ch, Head(n, nlogp))
        return
    end

    if z > 0
        sources = paths[z]
    else
        sources = paths[n.ind]
    end

    for tails in Channel{Tails}(channelsize) do nch
        groom(nch, G, sources, nlogp, budget + nlogp, paths)
    end
        n.children = tails.tails
        push!(ch, Head(deepcopy(n), tails.logp))
    end
end

function count_ghosts(G, tree::Gamma, ghost::Gamma)
    isterminal(G, tree) && return 0

    if isequal0(G, tree, ghost)
        c = 1
        for tail in tree.children
            c += count_ghosts(G, tail, ghost)
        end
        return c
    end

    c = 0
    for tail in tree.children
        c += count_ghosts(G, tail, ghost)
    end
    return c
end

function add!(G::Grammar, d::Gamma, rule::Expr)
    ind = length(G.rules) + 1

    childtypes = get_childtypes(rule, unique(G.types))
    type = return_type(G, d)
    is_terminal = isterminal(rule, collect(keys(G.bytype)))

    push!(G.rules, rule)
    push!(G.types, type)
    push!(G.isterminal, is_terminal)
    push!(G.iseval, false)
    push!(G.bytype[type], ind)
    push!(G.childtypes, childtypes)

    ind
end

function countholes(G::Grammar, d::Gamma)::UInt
    if ishole(G, d)
        return 1
    end

    if isterminal(G, d)
        return 0
    end

    sum(countholes(G, tail) for tail in d.children)
end

## everything has to be in the order since we got lazy with numbering $args
function extract_matches(G::Grammar, tree::Gamma, treeholed::Gamma)
    if ishole(G, treeholed)
        return [deepcopy(tree)]
    end

    isterminal(G, treeholed) && return []

    out = []
    for (tail, holedtail) in zip(tree.children, treeholed.children)
        append!(out, extract_matches(G, tail, holedtail))
    end

    out
end

import Base.replace!
# just don't forget to remap inds to the new G without holes
function replace!(G::Grammar, tree::Gamma, matchbranch::Gamma, newbranch::Gamma)
    if isequal0(G, tree, matchbranch)
        branch = deepcopy(newbranch)

        isempty(tree.children) && return branch

        args = extract_matches(G, tree, matchbranch)
        branch.children = deepcopy(args)
        return branch
    end

    qq = Queue{Gamma}()
    enqueue!(qq, tree)

    for n in qq
        isempty(n.children) && continue

        for ind in 1:length(n.children)
            if isequal0(G, n.children[ind], matchbranch)
                branch = deepcopy(newbranch)
                args = extract_matches(G, n.children[ind], matchbranch)
                branch.children = deepcopy(args)
                n.children[ind] = branch
            else
                enqueue!(qq, n.children[ind])
            end
        end
    end

    return tree
end

function pinholes(G::Grammar, GI::GrammarInfo, tree::Gamma)
    if ishole(G, tree)
        return [NodeLoc(tree,  0)]
    end

    out = []
    for (ind, tail) in enumerate(tree.children)
        if ishole(G, tail)
            push!(out, NodeLoc(tree, ind))
        else
            append!(out, pinholes(G, GI, tail))
        end
    end

    out
end

function isnormal(G::Grammar, GI::GrammarInfo, tree::Gamma)
    if tree.ind > GI.axiomlength
        return false
    end

    return all(isnormal(G, GI, tail) for tail in tree.children)
end

function normalize!(G::Grammar, GI::GrammarInfo, tree::Gamma)
    if tree.ind > GI.axiomlength
        body = deepcopy(GI.hiddentails[tree.ind])

        while !isnormal(G, GI, body)
            body = normalize!(G, GI, body)
        end

        if !isempty(tree.children)
            holelocs = pinholes(G, GI, body)

            # replace a single hole in the same order it was found
            for (loc, tail) in zip(holelocs, tree.children)
                insert!(body, loc, normalize!(G, GI, tail))
            end
        end

        return body
    end

    qq = Queue{Gamma}()
    enqueue!(qq, tree)

    for n in qq
        for (ind, tail) in enumerate(n.children)
            if tail.ind > GI.axiomlength
                body = deepcopy(GI.hiddentails[tail.ind])

                while !isnormal(G, GI, body)
                    body = normalize!(G, GI, body)
                end

                if !isempty(tail.children)
                    holelocs = pinholes(G, GI, body)

                    # replace a single hole in the same order it was found
                    for (loc, ntail) in zip(holelocs, tail.children)
                        insert!(body, loc, normalize!(G, GI, ntail))
                    end
                end

                n.children[ind] = body
            else
                enqueue!(qq, tail)
            end
        end
    end

    return tree
end

function displace!(tree::Gamma, mapping::Dict{Int, Int})
    if haskey(mapping, tree.ind)
        tree.ind = mapping[tree.ind]
    end

    map(d -> displace!(d, mapping), tree.children)
end

function splittree(G, tree)
    out = [tree]

    for tail in tree.children
        if !isterminal(G, tail)
            append!(out, splittree(G, tail))
        end
    end

    out
end

function bigcount(G, trees, ctrees)
    pbar = Progress(length(trees))

    nthreads = Threads.nthreads()

    dtrees = reduce(append!, [splittree(G, tree) for tree in trees])

    stats = [BinaryMinHeap{GhostStat}() for _ = 1:nthreads]
    ghosts = [Set{Gamma}() for _ = 1:nthreads]

    Threads.@threads for d in dtrees
        tid = Threads.threadid()

        for head in Channel{Head}(channelsize) do ch
            penumerate(ch, G, deepcopy(d), 0.0, Inf, marktree(G, d), z=1)
        end

            ghost = head.head

            c = 0
            # how many ghosts are in a single tree * how many times this tree appears
            for tree in trees
                c += count_ghosts(G, tree, ghost)
            end

            if length(stats[tid]) < 10
                push!(stats[tid], GhostStat(ghost, c))

            elseif c > first(stats[tid]).count
                if ghost ∉ ghosts[tid]
                    pop!(stats[tid])
                    push!(stats[tid], GhostStat(ghost, c))
                    push!(ghosts[tid], ghost)
                end
            end
        end

        next!(pbar)
    end

    ghostbuster = Dict{Gamma, Int}()
    for stat in stats
        for gstat in extract_all!(stat)
            ghostbuster[gstat.ghost] = gstat.count
        end
    end

    ghostbuster
end


function extract!(G::Grammar, GI::GrammarInfo, trees::Vector{Gamma}, ctrees)
    ghosttime = time()

    for type in Set(G.types)
        type ∉ G.rules && addhole!(G, type)
    end

    empty!(GI.hiddentails)
    GI.axiomlength = length(G)
    GI.length = 0

    while true
        ghostbuster = bigcount(G, trees, ctrees)
        mx = sum(map(length, trees))

        minκ = 1
        mind = nothing
        minc = 0

        for (ghost, c) in ghostbuster
            nargs = 1 + countholes(G, ghost)

            mxζ = mx - c * (length(ghost) - nargs)
            mζ = length(ghost)

            κ = (mxζ + mζ) / mx

            if κ < minκ
                minκ = κ
                mind = ghost
                minc = c
            end
        end

        if mind === nothing
            @printf "ghostting took %.1fm\n" (time() - ghosttime) / 60
            break
        end

        ind = add!(G, mind, get_executable(mind, G))
        GI.length += length(mind)
        GI.hiddentails[ind] = mind

        @printf "adding %s with %.2fκ # %d\n" fancy(G, mind) minκ minc
        trees = [replace!(G, tree, mind, Gamma(ind)) for tree in trees]
        ctrees = Dict(tree => c for (tree, c) in zip(trees, values(ctrees)))
    end

    trees
end

function processfirstkid(restmost, budget, paths, G, X, Z, rootind)
    c = 0
    stime = time()

    function accept(left::Tails)
        tZ = Z[Threads.threadid()]

        for rest in Channel{Tails}(channelsize) do ch
            groom(ch, G, restmost, left.logp, budget + left.logp, paths)
        end
            d = Gamma(rootind, [left.tails; rest.tails])
            s = Core.eval(d, G) |> collect
            c += 1

            # on multiple side
            for x in X
                if occursin(s, x)
                    if !haskey(tZ, s) || length(d) < length(tZ[s])
                        # @printf "[%d] * %s - %s {%.2f}\n" c s fancy(G, d) rest.logp
                        tZ[s] = deepcopy(d)
                    end

                    break
                end
            end

            if c % 1e7 == 0
                @printf "! %d\n" c / (time() - stime)
            end
        end
    end

    return accept
end

function ECD(G, X::Vector{T}; budget=15.0, timebudget=Inf) where T
    GI = GrammarInfo(Dict{Int, Gamma}(), length(G), 0, [])

    Q = log.(softmax(ones(length(G))))

    # multiple side
    cshards = mergewith!(+, Dict(), countshards.(X)...)

    totalshards = length(values(cshards))

    budgetind = 0

    oG = deepcopy(G)

    Z = Dict{Vector{Int64}, Gamma}()
    forests = nothing

    while !haskey(Z, X) && timebudget > 0
        c = 0
        stime = time()
        budget += 2 * budgetind
        # empty!(Z) # why?

        roots = filter(dind -> !ishole(G, dind), G.bytype[:List])
        Zs = [deepcopy(Z) for _ = 1:Threads.nthreads()]
        paths = makepaths(G, Q, forbidden)
        println("lumbering...")

        for rootind in roots
            sources = paths[rootind]

            if length(sources) < 2
                leftmost = sources
                restmost = []
            else
                leftmost = [sources[1]]
                restmost = sources[2:end]
            end

            Threads.foreach(processfirstkid(restmost, budget, paths, G, X, Zs, rootind),
                            Channel{Tails}(channelsize) do ch
                                groom(ch, G, leftmost, 0.0, budget, paths)
                            end)
        end

        @printf "hard work took %.1fm\n" (time() - stime) / 60
        mergewith!((a, b) -> ifelse(length(a) < length(b), a, b), Z, Zs...)

        for (x, d) in Z
            @assert collect(Core.eval(d, G)) == x
        end

        trees = values(Z)
        xlens = length.(keys(Z))
        treelen = length.(trees)

        println("amassed good! $(length(trees))/$totalshards")
        @printf "fish nature is (%.2f @ %d)\n" mean(xlens) maximum(xlens)
        @printf "tree nature is (%.2f @ %d)\n" mean(treelen) maximum(treelen)

        W = Dict(join(w, "") => 1 for (w, g) in Z)

        # multi-x
        forests = []

        for x in X
            forest = deepcopy(flatvase(join(x, ""), Z, W) |> reverse)

            outx = reduce(append!, [collect(Core.eval(tree, G)) for tree in forest])
            #@show outx, x
            @assert outx == x

            push!(forests, forest)
        end

        for (w, d) in Z
            # @show w, d, Core.eval(d, G)
            @assert collect(Core.eval(d, G)) == w
        end

        for (x, forest) in zip(X, forests)
            mxg = sum(length.(forest))
            @show mxg, GI.length, (mxg + GI.length) / length(x)

            if length(x) > 1
                println(x[1:20])
            end

            for tree in forest
                println("$tree $(Core.eval(tree, G))")
            end
        end

        timebudget -= (time() - stime) / 60

	    if timebudget < 0
            return Dict(zip(X, forests)), G, GI
	    end

        trees = reduce(append!, deepcopy(forests))

        outtrees = [collect(Core.eval(g, G)) for g in trees]

        normtrees = [normalize!(G, GI, tree) for tree in trees]

        ctrees = Dict(normtree => cshards[x] for (x, normtree) in zip(keys(Z), normtrees))
        normtrees = reduce(append!, [splittree(G, ntree) for ntree in normtrees])

        treelen = length.(normtrees)

        @printf "tree drying is (%.2f @ %d)\n" mean(treelen) maximum(treelen)

        # G reset
        # G = deepcopy(oG)
        trees = extract!(G, GI, deepcopy(normtrees), ctrees)

        for (ntree, tree) in zip(normtrees, trees)
            @assert collect(Core.eval(ntree, oG)) == collect(Core.eval(tree, G))
        end

        Q = log.(softmax(ones(length(G))))
        Z = Dict(collect(Core.eval(g, G)) => g for g in trees)

        for (w, g) in Z
            @show w, g, Core.eval(g, G)
            @assert collect(Core.eval(g, G)) == w
        end

        println(G)
        budgetind += 1
    end

    return Dict(zip(X, forests)), G, GI
end

# ■ ~

import Base.repeat
function repeat(xs::Cons{Int64}, n::Int)
    cat([xs for _ = 1:n]...)
end

function getindex(::Nil{T}, ::Int) where T
    nil(T)
end

G = @grammar begin
    List = cat(List, List)
    Nat = Nat + Nat
    List = list(0) | list(1)
    List = repeat(List, Nat)
    Nat = 2 | 3
end

forbidden = Dict(ind => [] for ind in 1:length(G))
forbidden[1] = [(argind -> argind != 2, 1), (argind -> argind != 2, 3)]
forbidden[2] = [(argind -> argind != 2, 2)]

onsetted = read("stash/onsetted.json", String) |> JSON.parse
onsettedinv = Dict(zip(values(onsetted), keys(onsetted)))

for birb in keys(onsetted)
    @assert birb == onsettedinv[onsetted[birb]]
end

X = map(x -> Int.(x), values(onsetted))
# ■ ~

forests, G, GI = ECD(G, X, budget=16, timebudget=60)
@save "stash/forests.bson" forests G GI

# ■ ~

@load "stash/forests.bson" forests G GI

forestdata = Dict()

for (birb, onsets) in onsetted
    println(birb)

    println(length(onsets))
    mxζ = sum(length.(forests[onsets])) + length(forests[onsets]) - 1
    @show mxζ

    for tree in forests[onsets]
        println(tree)
    end

    forestdata[birb] = [mxζ, onsets]
end

write("forestdata.json", JSON.json(forestdata))
