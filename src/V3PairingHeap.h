// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Pairing Heap data structure
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3PAIRINGHEAP_H_
#define VERILATOR_V3PAIRINGHEAP_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

//=============================================================================
// Pairing heap (max-heap) with increase key and delete.
//
// While this is written as a generic data structure, it's interface and
// implementation is finely tuned for it's use by V3Parm_tition, and is critical
// to verilaton performance, so be very careful changing anything or adding any
// new operations that would impact either memory usage, or performance of the
// existing operations. This data structure is fully deterministic, meaning
// the order in which elements with equal keys are retrieved only depends on
// the order of operations performed on the heap.
//=============================================================================

template <typename T_Key>
class PairingHeap final {
public:
    struct Node;

    // Just a pointer to a heap Node, but with special accessors to help keep back pointers
    // consistent.
    struct Link {
        Node* m_ptr = nullptr;  // The managed pointer

        Link() = default;
        VL_UNCOPYABLE(Link);

        // Make the pointer point to the target, and the target's owner pointer to this pointer
        void link(Node* targetp) {
            m_ptr = targetp;
            if (!targetp) return;
#if VL_DEBUG
            UASSERT(!targetp->m_ownerpp, "Already linked");
#endif
            targetp->m_ownerpp = &m_ptr;
        }

        // Clear the pointer and return it's previous value
        Node* unlink() {
            Node* const result = m_ptr;
#if VL_DEBUG
            if (result) {
                UASSERT(m_ptr->m_ownerpp == &m_ptr, "Bad back link");
                // Not strictly necessary to clear this, but helps debugging
                m_ptr->m_ownerpp = nullptr;
            }
#endif
            m_ptr = nullptr;
            return result;
        }

        // Minimal convenience acessors and operators
        Node* ptr() const { return m_ptr; }
        operator bool() const { return m_ptr; }
        bool operator!() const { return !m_ptr; }
        Node* operator->() const { return m_ptr; }
        Node& operator*() const { return *m_ptr; }
    };

    // A single node in the pairing heap tree
    struct Node {
        Link m_next;  // Next in list of sibling heaps
        Link m_kids;  // Head of list of child heaps
        Node** m_ownerpp = nullptr;  // Pointer to the Link pointer pointing to this heap
        T_Key m_key;  // The key in the heap

        // CONSTRUCTOR
        explicit Node() = default;
        VL_UNCOPYABLE(Node);

        // METHODS
        const T_Key& key() const { return m_key; }
        bool operator<(const Node& that) const { return m_key < that.m_key; }
        bool operator>(const Node& that) const { return that.m_key < m_key; }

        // Make newp take the place of this in the tree
        void replaceWith(Node* newp) {
#if VL_DEBUG
            UASSERT(m_ownerpp, "Not linked");
#endif
            *m_ownerpp = newp;  // The owner pointer needs to point to the new node
            if (newp) newp->m_ownerpp = m_ownerpp;  // The new node needs to point to its owner
            m_ownerpp = nullptr;  // This node has no owner anymore
        }
    };

private:
    // MEMBERS
    mutable Link m_root;  // The root of the heap

    // CONSTRUCTORS
    VL_UNCOPYABLE(PairingHeap);

public:
    explicit PairingHeap() = default;

    // METHODS
    bool empty() const { return !m_root; }

    // Insert given node into this heap with given key.
    void insert(Node* nodep, T_Key key) {
        // Update key of node
        nodep->m_key = key;
        insert(nodep);
    }

    // Insert given node into this heap with key already set in the node
    void insert(Node* nodep) {
#if VL_DEBUG
        UASSERT(!nodep->m_ownerpp && !nodep->m_next && !nodep->m_kids, "Already linked");
#endif
        if (VL_UNLIKELY(!m_root)) {
            // If no root (first node), this becomes the root
            nodep->m_next.link(nullptr);
            nodep->m_kids.link(nullptr);
            m_root.link(nodep);
            return;
        }
        // If the root have siblings reduce them so we can compare the new element
        if (m_root->m_next) m_root.link(reduce(m_root.unlink()));
        // Compare with the now singular root
        if (*nodep > *m_root) {
            // If the new node is bigger than the root, the new node becomes the root
            Node* const rootp = m_root.ptr();
            m_root->replaceWith(nodep);
            nodep->m_next.link(nullptr);
            nodep->m_kids.link(rootp);
        } else {
            // Otherwise the new node goes under the root
            nodep->m_next.link(m_root->m_kids.unlink());
            nodep->m_kids.link(nullptr);
            m_root->m_kids.link(nodep);
        }
    }

    // Remove given node only from the heap it is contained in
    void remove(Node* nodep) {
        // Note: We do not reduce lists during removal. This means the root can sometimes become
        // a list. This is ok, we will reduce it when accessing the minimum. Also, this method
        // could be static as we have the owner pointer in the nodes, but we keep it for safety
        // as it mutates the heap.
        if (!nodep->m_next) {
            // If the node does not have siblings, replace it with its children (might be empty).
            nodep->replaceWith(nodep->m_kids.unlink());
        } else if (!nodep->m_kids) {
            // If it has siblings but no children, replace it with the siblings.
            nodep->replaceWith(nodep->m_next.unlink());
        } else {
            // If it has both siblings and children, reduce and merge them, then replace
            Node* const reducedNextp = reduce(nodep->m_next.unlink());
            Node* const reducedKidsp = reduce(nodep->m_kids.unlink());
            nodep->replaceWith(merge(reducedNextp, reducedKidsp));
        }
    }

    // Returns the largest element in the heap
    Node* max() const {
        // Heap might be empty
        if (!m_root) return nullptr;
        // If the root have siblings reduce them
        if (m_root->m_next) m_root.link(reduce(m_root.unlink()));
        // The root element is the largest
        return m_root.ptr();
    }

    // Returns the second-largest element in the heap.
    // This is only valid to call if 'max' returned a valid element.
    Node* secondMax() const {
#if VL_DEBUG
        UASSERT(m_root, "'max' would have returned nullptr");
        UASSERT(!m_root->m_next, "'max' would have reduced");
#endif
        // If there are no children, there is no second element
        if (!m_root->m_kids) return nullptr;
        // If there are multiple children, reduce them
        if (m_root->m_kids->m_next) m_root->m_kids.link(reduce(m_root->m_kids.unlink()));
        // Return the now singular child, which is the second-largest element
        return m_root->m_kids.ptr();
    }

    // Increase the key of the given node to the given new value
    template <typename T_Update>
    void increaseKey(Node* nodep, T_Update value) {
        // Update the key
        nodep->m_key.increase(value);
        // Increasing the key of the root is easy
        if (nodep == m_root.ptr()) return;
        // Otherwise we do have a little work to do
        if (!nodep->m_kids) {
            // If the node has no children, replace it with its siblings
            nodep->replaceWith(nodep->m_next.unlink());
        } else if (!nodep->m_next) {
            // If the node has no siblings, replace it with its children
            nodep->replaceWith(nodep->m_kids.unlink());
        } else {
            // The node has both children and siblings. Splice the first child in the place of the
            // node, and extract the rest of the children with the node
            Node* const childp = nodep->m_kids.unlink();
            nodep->m_kids.link(childp->m_next.unlink());
            childp->m_next.link(nodep->m_next.unlink());
            nodep->replaceWith(childp);
        }
        // If the root has siblings, reduce them
        if (m_root->m_next) m_root.link(reduce(m_root.unlink()));
        // Meld the node with the root
        m_root.link(merge(nodep, m_root.unlink()));
    }

private:
    // Meld (merge) two heaps rooted at the given nodes, return the root of the new heap
    static Node* merge(Node* ap, Node* bp) {
#if VL_DEBUG
        UASSERT(!ap->m_ownerpp && !ap->m_next, "Not root a");
        UASSERT(!bp->m_ownerpp && !bp->m_next, "Not root b");
#endif
        if (*ap > *bp) {  // bp goes under ap
            bp->m_next.link(ap->m_kids.unlink());
            ap->m_kids.link(bp);
            return ap;
        } else {  // ap goes under bp
            ap->m_next.link(bp->m_kids.unlink());
            bp->m_kids.link(ap);
            return bp;
        }
    }

    // Reduces the list of nodes starting at the given node into a single node that is returned
    static Node* reduce(Node* nodep) {
#if VL_DEBUG
        UASSERT(!nodep->m_ownerpp, "Node is linked");
#endif
        // If there is only one node in the list, then there is nothing to do
        if (!nodep->m_next) return nodep;
        // The result node
        Node* resultp = nullptr;
        // Pairwise merge the child nodes
        while (nodep) {
            // Pop off the first nodes
            Node* const ap = nodep;
            // If we have an odd number of nodes, prepend the unpaired one onto the result list
            if (!nodep->m_next) {
                ap->m_next.link(resultp);
                resultp = ap;
                break;
            }
            // Pop off the second nodes
            Node* const bp = nodep->m_next.unlink();
            // Keep hold of the rest of the list
            nodep = bp->m_next.unlink();
            // Merge the current pair
            Node* const mergedp = merge(ap, bp);
            // Prepend the merged pair to the result list
            mergedp->m_next.link(resultp);
            resultp = mergedp;
        }
        // Now merge-reduce the merged pairs
        while (resultp->m_next) {
            // Pop first two results
            Node* const ap = resultp;
            Node* const bp = resultp->m_next.unlink();
            // Keep hold of the rest of the list
            resultp = bp->m_next.unlink();
            // Merge the current pair
            Node* const mergedp = merge(ap, bp);
            // Prepend the merged pair to the result list
            mergedp->m_next.link(resultp);
            resultp = mergedp;
        }
        // Done
        return resultp;
    }
};

// The PairingHeap itself should be a simple pointer and nothing more
static_assert(sizeof(PairingHeap<int>) == sizeof(PairingHeap<int>::Node*), "Should be a pointer");

#endif  // Guard
